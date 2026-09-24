from __future__ import annotations

from contextlib import redirect_stdout, redirect_stderr
import importlib.util
from io import StringIO
import json
from pathlib import Path
import shutil
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("emdash_devops", Path(__file__).with_name("devops.py"))
devops = importlib.util.module_from_spec(spec)
spec.loader.exec_module(devops)


class DevOpsTests(unittest.TestCase):
    def test_document_links_preserve_code_labels_but_ignore_inline_math_code(self):
        self.assertEqual(devops.markdown_links(
            '[`owner.ts`](owner.ts) and `F[x](y)`\n```text\n[example](missing)\n```\n[guide](guide.md)'
        ), ['owner.ts', 'guide.md'])

    def gates(self, *paths):
        return {row["gate"] for row in devops.select_gates(list(paths))["include"]}

    def test_document_changes_do_not_select_semantic_or_render_aggregates(self):
        self.assertEqual(self.gates("docs/review.md", "README.md"), {"docs"})

    def test_nested_lp_and_semantic_typescript_changes_widen_validation(self):
        self.assertTrue({"formal", "conformance", "scale-conformance"} <= self.gates("emdash2/examples/example.lp"))
        self.assertNotIn("formal-smoke", self.gates("emdash2/emdash3_2.lp"))
        self.assertTrue({"typescript", "package", "reviewer", "conformance", "scale-conformance"}
                        <= self.gates("src/v3_2/checker.ts"))

    def test_runner_and_print_changes_preserve_their_own_boundaries(self):
        self.assertIn("formal-smoke", self.gates("emdash2/scripts/check_registry.py"))
        self.assertNotIn("formal", self.gates("emdash2/scripts/check_registry.py"))
        self.assertEqual(self.gates("emdash2/book/chapters/01-introduction.md"), {"docs", "book"})
        self.assertEqual(self.gates("emdash2/print/src/App.tsx"), {"docs", "print"})

    def test_unknown_paths_fail_closed_into_full_selection(self):
        expected = {row["gate"] for row in devops.select_gates([], full=True)["include"]}
        self.assertEqual(self.gates("new-system/engine.rs"), expected)

    def test_validation_policy_changes_cannot_reuse_a_narrow_gate_set(self):
        expected = {row["gate"] for row in devops.select_gates([], full=True)["include"]}
        for name in ("devops/gates.json", "scripts/devops.py", ".github/workflows/validate.yml"):
            with self.subTest(name=name):
                self.assertEqual(self.gates(name), expected)

    def test_tooling_receipts_fingerprint_the_publication_policy_under_test(self):
        inputs = devops.gate_inputs(devops.contract()["gates"]["tooling"])
        for name in (".github/scripts/validation_artifacts.py", ".github/workflows/validate.yml",
                     ".github/workflows/pages.yml"):
            self.assertIn(name, inputs)

    def test_no_basename_aliasing_or_duplicate_commands(self):
        self.assertFalse(devops.matches("vendor/package.json", "package.json"))
        self.assertFalse(devops.matches("emdash2/audits/private.lp", "emdash2/*.lp"))
        plan = devops.select_gates(["package.json", "package.json", "src/v3_2/probe.ts"])
        names = [row["gate"] for row in plan["include"]]
        self.assertEqual(len(names), len(set(names)))

    def test_empty_required_gate_is_invalid(self):
        data = devops.contract()
        data["gates"]["docs"]["commands"] = []
        with patch.object(devops.json, "loads", return_value=data), self.assertRaisesRegex(ValueError, "no commands"):
            devops.contract()

    def test_failed_gate_stops_and_persists_failure(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            marker = root / "must-not-run"
            gate = {"commands": [[sys.executable, "-c", "raise SystemExit(7)"],
                                 [sys.executable, "-c", f"open({str(marker)!r}, 'w').close()"]],
                    "inputs": [], "timeoutSeconds": 5}
            with patch.object(devops, "ROOT", root), patch.object(devops, "contract", return_value={"gates": {"fixture": gate}}), \
                 patch.object(devops, "gate_inputs", return_value={}), patch.object(devops, "revision", return_value="baseline"), \
                 redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                receipt = devops.run_gate("fixture", [])
            self.assertFalse(marker.exists())
            self.assertEqual(receipt["outcome"], "failed")
            self.assertEqual(len(receipt["commands"]), 1)
            saved = next((root / "emdash2/logs/devops").glob("*.json"))
            self.assertEqual(json.loads(saved.read_text())["commands"][0]["exit"], 7)

    def test_success_with_changed_inputs_is_not_passed(self):
        with TemporaryDirectory() as directory:
            gate = {"commands": [[sys.executable, "-c", "pass"]], "timeoutSeconds": 5}
            with patch.object(devops, "ROOT", Path(directory)), patch.object(devops, "contract", return_value={"gates": {"fixture": gate}}), \
                 patch.object(devops, "gate_inputs", side_effect=[{"input": "before"}, {"input": "after"}]), \
                 patch.object(devops, "revision", return_value="baseline"), redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                self.assertEqual(devops.run_gate("fixture", [])["outcome"], "inputs-changed")

    @unittest.skipUnless(sys.platform == "linux" and shutil.which("node"), "Linux/Node process-group check")
    def test_deadline_stops_reporter_and_busy_test_worker_without_claiming_success(self):
        reporter = Path(__file__).with_name("test-progress.mjs").resolve()
        with TemporaryDirectory() as directory:
            root = Path(directory)
            worker_pid = root / "worker.pid"
            fixture = root / "busy.mjs"
            fixture.write_text(
                "import test from 'node:test'; import { writeFileSync } from 'node:fs';\n"
                "test('busy worker', () => {\n"
                f"writeFileSync({json.dumps(str(worker_pid))}, String(process.pid));\n"
                "while (true) {}\n});\n"
            )
            gate = {"commands": [[shutil.which("node"), "--test", "--test-reporter=" + str(reporter), str(fixture)]],
                    "timeoutSeconds": 1}
            with patch.object(devops, "ROOT", root), patch.object(devops, "contract", return_value={"gates": {"fixture": gate}}), \
                 patch.object(devops, "gate_inputs", return_value={}), patch.object(devops, "revision", return_value="baseline"), \
                 patch.dict(devops.os.environ, {"EMDASH_TEST_PROGRESS_INTERVAL_MS": "50"}), \
                 redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                receipt = devops.run_gate("fixture", [])
            self.assertEqual(receipt["outcome"], "timeout")
            self.assertEqual(receipt["commands"][0]["exit"], 124)
            self.assertIn("[progress] parent alive", (root / receipt["log"]).read_text())
            pid = int(worker_pid.read_text())
            state = Path(f"/proc/{pid}/stat")
            try:
                self.assertEqual(state.read_text().split()[2], "Z", "worker still running")
            except FileNotFoundError:
                pass  # The exited worker has already been reaped.


if __name__ == "__main__":
    unittest.main()
