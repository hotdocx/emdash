from __future__ import annotations

from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from scripts.check_registry import (
    ROOT, digest_inputs, input_hashes, inventory_issues, load_registry,
    profile_for, source_closure,
)


class CheckRegistryTests(unittest.TestCase):
    def test_current_inventory_is_complete_and_imports_resolve(self):
        data = load_registry()
        self.assertEqual(inventory_issues(data), [])
        paths = [Path(p) for p in data["core"] + data["reviewers"]]
        self.assertEqual(set(source_closure(paths)), set(paths))
        self.assertIn("emdash3_2_prof_reindex_terminal_normalization.lp", data["core"])

    def test_unregistered_source_is_reported(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "added.lp").write_text("symbol a : TYPE;")
            self.assertEqual(inventory_issues({"core": [], "reviewers": []}, root),
                             ["unregistered core source: added.lp"])

    def test_transitive_import_and_resolution_changes_invalidate_snapshot(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lambdapi.pkg").write_text("root_path = test\n")
            (root / "parent.lp").write_text("symbol left : TYPE;\n")
            (root / "middle.lp").write_text("require open test.parent;\n")
            (root / "reviewer.lp").write_text("require test.middle;\n")
            target = [Path("reviewer.lp")]
            before = digest_inputs(input_hashes(target, root))
            (root / "parent.lp").write_text("symbol rite : TYPE;\n")
            changed = digest_inputs(input_hashes(target, root))
            self.assertNotEqual(before, changed)
            (root / "lambdapi.pkg").write_text("root_path = test\npackage_name = renamed\n")
            self.assertNotEqual(changed, digest_inputs(input_hashes(target, root)))
            (root / "parent.lpo").write_bytes(b"compiled parent")
            self.assertIn("parent.lpo", input_hashes(target, root, objects=True))
            self.assertNotIn("parent.lpo", input_hashes(target, root))

    def test_multiple_imports_ignore_comments_and_strings(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lambdapi.pkg").write_text("root_path = test\n")
            for name in ("a", "b"):
                (root / (name + ".lp")).write_text("symbol a : TYPE;")
            (root / "reviewer.lp").write_text('''
/* "quoted /* inner */ // not a line comment */
// require bogus.missing;
require open test.a test.b;
"require missing.false;"
''')
            self.assertEqual(source_closure([Path("reviewer.lp")], root),
                             [Path("a.lp"), Path("b.lp"), Path("reviewer.lp")])

    def test_unresolved_or_external_imports_cannot_produce_evidence(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lambdapi.pkg").write_text("root_path = test\n")
            for source in ("require test.missing;", "require external.unknown;",
                           "require open;", "require test.missing"):
                with self.subTest(source=source):
                    (root / "test.lp").write_text(source)
                    with self.assertRaises(ValueError):
                        input_hashes([Path("test.lp")], root)

    def test_profile_selection_is_exact_and_does_not_widen_by_filename(self):
        data = load_registry()
        name, profile = profile_for(Path("examples/freyd_native_snake_pair_exactness.lp"), data)
        self.assertEqual(name, "native-snake-pair")
        self.assertEqual((profile["memoryMiB"], profile["timeoutSeconds"]), (6144, 180))
        self.assertEqual(profile_for(Path("tmp/freyd_native_snake_pair_exactness.lp"), data)[0], "default")

    def test_registry_rejects_duplicate_profile_membership(self):
        data = load_registry()
        data["profileTargets"]["native-six-term"].append(data["profileTargets"]["native-snake-pair"][0])
        # Validate schema against actual source paths without copying mathematical inputs.
        from unittest.mock import patch
        with patch("scripts.check_registry.json.loads", return_value=data):
            with self.assertRaisesRegex(ValueError, "overlapping profile"):
                load_registry(ROOT)

    def test_reviewed_memory_ceiling_is_bounded(self):
        from unittest.mock import patch
        data = load_registry()
        data["profiles"]["default"]["memoryMiB"] = 8192
        with patch("scripts.check_registry.json.loads", return_value=data):
            self.assertEqual(load_registry(ROOT)["profiles"]["default"]["memoryMiB"], 8192)
        data["profiles"]["default"]["memoryMiB"] = 8193
        with patch("scripts.check_registry.json.loads", return_value=data):
            with self.assertRaisesRegex(ValueError, "out-of-bounds profile"):
                load_registry(ROOT)


if __name__ == "__main__":
    unittest.main()
