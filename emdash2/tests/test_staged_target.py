from contextlib import redirect_stdout, redirect_stderr
from io import StringIO
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from scripts.check_staged_target import check_registered_stage


class RegisteredStageTests(unittest.TestCase):
    def setUp(self):
        self.temp = TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "formal"
        self.stage = Path(self.temp.name) / "stage"
        for root in [self.root, self.stage]:
            root.mkdir()
            (root / "lambdapi.pkg").write_text("root_path = test\n")
            (root / "parent.lp").write_text("symbol parent : TYPE;\n")
            (root / "target.lp").write_text("require test.parent;\n")
        registry = {"version": 1, "core": ["parent.lp", "target.lp"], "reviewers": [],
                    "check": [], "priority": [], "isolatedGroups": [], "profileTargets": {},
                    "profiles": {"default": {"memoryMiB": 2048, "timeoutSeconds": 90},
                                 "measured": {"memoryMiB": 3072, "timeoutSeconds": 180,
                                              "ocamlrunparam": "o=20"}},
                    "targetProfileOverrides": {"target.lp": "measured"}}
        (self.root / "checks.json").write_text(json.dumps(registry))
        self.calls = []

    def check(self, target=Path("target.lp"), **kwargs):
        with redirect_stdout(StringIO()), redirect_stderr(StringIO()):
            return check_registered_stage(target, self.stage, formal_root=self.root, **kwargs)

    def fake(self, target, root, **kwargs):
        self.calls.append((target, root, kwargs, dict(os.environ)))
        if kwargs.get("compile_object"):
            (root / target.with_suffix(".lpo")).write_bytes(b"checked fixture object")
        return {"id": "fixture", "outcome": "passed-fresh", "checkerExit": 0, "wallSeconds": 0.1}

    def test_exact_copy_selects_profile_and_restores_environment(self):
        with patch.dict(os.environ, {"KEEP": "value"}, clear=True), patch("scripts.check_staged_target.run_check", self.fake):
            self.assertEqual(self.check(compile_object=True), 0)
            self.assertEqual(dict(os.environ), {"KEEP": "value"})
        self.assertEqual([row[0] for row in self.calls], [Path("parent.lp"), Path("target.lp")])
        self.assertEqual(self.calls[0][3]["EMDASH_LP_MEMORY_MIB"], "2048")
        _, root, options, env = self.calls[-1]
        self.assertEqual(root, self.stage)
        self.assertTrue(options["compile_object"])
        self.assertEqual((env["EMDASH_LP_MEMORY_MIB"], env["EMDASH_LP_TIMEOUT"], env["OCAMLRUNPARAM"]),
                         ("3072", "180s", "o=20"))

    def test_explicit_limits_override_profile_and_default_stays_default(self):
        with patch.dict(os.environ, {"EMDASH_LP_MEMORY_MIB": "4096", "EMDASH_TYPECHECK_TIMEOUT": "240s"}, clear=True), patch("scripts.check_staged_target.run_check", self.fake):
            self.assertEqual(self.check(), 0)
        env = self.calls[-1][3]
        self.assertEqual((env["EMDASH_LP_MEMORY_MIB"], env["EMDASH_LP_TIMEOUT"]), ("4096", "240s"))
        with patch.dict(os.environ, {}, clear=True), patch("scripts.check_staged_target.run_check", self.fake):
            self.assertEqual(self.check(Path("parent.lp")), 0)
        env = self.calls[-1][3]
        self.assertEqual((env["EMDASH_LP_MEMORY_MIB"], env["EMDASH_LP_TIMEOUT"]), ("2048", "90s"))

    def test_changed_parent_or_package_is_rejected_before_runner(self):
        for name, changed in [("parent.lp", "symbol changed : TYPE;\n"),
                              ("lambdapi.pkg", "root_path = test\npackage_name = changed\n")]:
            before = (self.stage / name).read_text()
            (self.stage / name).write_text(changed)
            with self.subTest(name=name), patch("scripts.check_staged_target.run_check") as run:
                with self.assertRaisesRegex(ValueError, "differ"):
                    self.check()
                run.assert_not_called()
            (self.stage / name).write_text(before)

    def test_unregistered_path_cannot_acquire_profile_by_basename(self):
        with patch("scripts.check_staged_target.run_check") as run:
            with self.assertRaisesRegex(ValueError, "registered target"):
                self.check(Path("tmp/target.lp"))
            run.assert_not_called()

    def test_primary_source_change_rejects_current_qualification(self):
        def mutate(*args, **kwargs):
            result = self.fake(*args, **kwargs)
            (self.root / "parent.lp").write_text("symbol changed : TYPE;\n")
            return result
        with patch("scripts.check_staged_target.run_check", mutate):
            self.assertEqual(self.check(), 74)

    def test_staged_source_change_rejects_current_qualification(self):
        def mutate(*args, **kwargs):
            result = self.fake(*args, **kwargs)
            (self.stage / "target.lp").write_text("symbol changed : TYPE;\n")
            return result
        with patch("scripts.check_staged_target.run_check", mutate):
            self.assertEqual(self.check(compile_object=True), 74)

    def test_empty_existing_parent_object_is_rejected(self):
        (self.stage / "parent.lpo").touch()
        with patch("scripts.check_staged_target.run_check") as run:
            with self.assertRaisesRegex(ValueError, "empty staged object"):
                self.check(compile_object=True)
            run.assert_not_called()

    def test_empty_compilation_is_rejected(self):
        result = {"id": "fixture", "outcome": "passed-fresh", "checkerExit": 0, "wallSeconds": 0.1}
        with patch("scripts.check_staged_target.run_check", return_value=result):
            self.assertEqual(self.check(compile_object=True), 1)

    def test_failed_checker_is_not_success(self):
        result = {"id": "fixture", "outcome": "failed", "checkerExit": 7, "wallSeconds": 0.1}
        with patch("scripts.check_staged_target.run_check", return_value=result):
            self.assertEqual(self.check(), 7)


if __name__ == "__main__":
    unittest.main()
