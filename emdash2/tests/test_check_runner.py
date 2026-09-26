from __future__ import annotations

import json
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import os
from pathlib import Path
import shutil
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from scripts.run_lambdapi import ROOT, execution_settings, main, run_check, run_staged_group


class CheckRunnerTests(unittest.TestCase):
    def setUp(self):
        self.directory = TemporaryDirectory(prefix="emdash-runner-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "bin").mkdir()
        (self.root / "scripts").mkdir()
        shutil.copy(ROOT / "scripts/lambdapi_resource_guard.sh", self.root / "scripts")
        (self.root / "checks.json").write_text('{}')
        (self.root / "lambdapi.pkg").write_text('root_path = test\n')
        (self.root / "target.lp").write_text('symbol a : TYPE;\n')
        self.binary = self.root / "bin/lambdapi"
        env = {key: value for key, value in os.environ.items()
               if not key.startswith("EMDASH_") and key not in {"OCAMLRUNPARAM", "CAMLRUNPARAM"}}
        env.update(PATH=str(self.root / "bin") + os.pathsep + os.environ["PATH"],
                   XDG_RUNTIME_DIR=str(self.root), EMDASH_LP_RESOURCE_BACKEND="prlimit",
                   EMDASH_LP_MEMORY_MIB="64")
        self.environment = patch.dict(os.environ, env, clear=True)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.runner_root = patch("scripts.run_lambdapi.ROOT", self.root)
        self.runner_root.start()
        self.addCleanup(self.runner_root.stop)

    def checker(self, body):
        self.binary.write_text('#!/usr/bin/env python3\nimport sys\n'
                               'if "--version" in sys.argv:\n print("test-checker");sys.exit(0)\n' + body)
        self.binary.chmod(0o755)

    def test_real_child_receives_limits_and_receipt_retains_sources(self):
        self.checker('import resource\n'
                     'assert resource.getrlimit(resource.RLIMIT_AS)[0]==64*1024**2\n'
                     'print("raw checker output")\n')
        receipt = run_check(Path("target.lp"), self.root, timeout_ms=5000)
        self.assertEqual(receipt["outcome"], "passed-fresh")
        self.assertTrue(receipt["reusable"])
        self.assertEqual(receipt["observedResourceBackend"], "prlimit")
        self.assertIn("raw checker output", (self.root / receipt["log"]).read_text())
        saved = json.loads(Path(receipt["receiptPath"]).read_text())
        self.assertEqual(saved["id"], receipt["id"])
        digest = receipt["inputs"]["target.lp"]
        self.assertEqual((self.root / receipt["inputStore"] / digest).read_text(), 'symbol a : TYPE;\n')

    def test_failure_and_hard_timeout_never_produce_reusable_success(self):
        self.checker('print("deliberate error");sys.exit(7)\n')
        failure = run_check(Path("target.lp"), self.root, timeout_ms=5000)
        self.assertEqual(failure["checkerExit"], 7)
        self.assertEqual(failure["outcome"], "failed")
        self.assertFalse(failure["reusable"])
        self.checker('import signal,time\nsignal.signal(signal.SIGINT,signal.SIG_IGN)\ntime.sleep(20)\n')
        timeout = run_check(Path("target.lp"), self.root, timeout_ms=1000)
        self.assertEqual(timeout["outcome"], "timeout")
        self.assertLess(timeout["wallSeconds"], 5)
        self.assertFalse(timeout["reusable"])

    def test_input_change_during_success_invalidates_receipt(self):
        self.checker('from pathlib import Path\nPath("target.lp").write_text("symbol b : TYPE;\\n")\n')
        result = run_check(Path("target.lp"), self.root, timeout_ms=5000)
        self.assertEqual(result["checkerExit"], 0)
        self.assertEqual(result["outcome"], "inputs-changed")
        self.assertFalse(result["reusable"])

    def test_zero_exit_serialization_failure_is_rejected_by_receipt_and_cli(self):
        self.checker('from pathlib import Path\n'
                     'Path("target.lpo").touch()\n'
                     'print("Uncaught [Out of memory].")\n')
        result = run_check(Path("target.lp"), self.root, timeout_ms=5000, compile_object=True)
        self.assertEqual(result["checkerExit"], 0)
        self.assertEqual(result["outcome"], "allocation-failed")
        self.assertFalse(result["reusable"])
        self.assertEqual((self.root / "target.lpo").stat().st_size, 0)
        stdout, stderr = StringIO(), StringIO()
        argv = ["run_lambdapi.py", "--quiet", "--compile", "--package-root", str(self.root), "target.lp"]
        with patch.object(sys, "argv", argv), redirect_stdout(stdout), redirect_stderr(stderr):
            code = main()
        self.assertEqual(code, 1)
        self.assertIn("allocation-failed", stdout.getvalue())
        self.assertIn("Uncaught [Out of memory].", stderr.getvalue())

    def test_fatal_diagnostics_override_zero_exit_and_input_change_status(self):
        for diagnostic, expected in (
            ("Uncaught [End_of_file].", "failed"),
            ("\x1b[31mFatal error: allocation failure during minor GC\x1b[0m", "allocation-failed"),
        ):
            with self.subTest(diagnostic=diagnostic):
                (self.root / "target.lp").write_text('symbol original : TYPE;\n')
                self.checker('from pathlib import Path\n'
                             'Path("target.lp").write_text("symbol changed : TYPE;\\n")\n'
                             f'print({diagnostic!r})\n')
                result = run_check(Path("target.lp"), self.root, timeout_ms=5000)
                self.assertEqual(result["checkerExit"], 0)
                self.assertEqual(result["outcome"], expected)
                self.assertFalse(result["reusable"])

    def test_profiles_and_explicit_limits_are_resolved_without_running(self):
        target = Path("examples/freyd_native_snake_pair_exactness.lp")
        profile = execution_settings(target, {})
        self.assertEqual((profile["memoryMiB"], profile["timeoutMs"], profile["ocamlrunparam"]),
                         (6144, 180000, "o=20"))
        overridden = execution_settings(target, {"EMDASH_LP_MEMORY_MIB": "4096", "EMDASH_PROBE_TIMEOUT": "120s"})
        self.assertEqual((overridden["memoryMiB"], overridden["timeoutMs"]), (4096, 120000))
        expanded = execution_settings(target, {"EMDASH_LP_MEMORY_MIB": "8192", "EMDASH_LP_TIMEOUT": "600s"})
        self.assertEqual((expanded["memoryMiB"], expanded["timeoutMs"]), (8192, 600000))
        self.assertEqual(execution_settings(Path("ordinary.lp"), {})["memoryMiB"], 2048)
        for env in ({"EMDASH_LP_MEMORY_MIB": "8193"}, {"EMDASH_LP_TIMEOUT": "601s"},
                    {"EMDASH_LAMBDAPI_FLAGS": "--no-sr-check"}):
            with self.subTest(env=env), self.assertRaises(ValueError):
                execution_settings(target, env)

    def test_staged_recipe_preserves_failure_and_records_group_scope(self):
        script = self.root / "scripts/group.sh"
        script.write_text('#!/bin/sh\nexec bash scripts/lambdapi_resource_guard.sh lambdapi check target.lp\n')
        script.chmod(0o755)
        self.checker('print("staged failure");sys.exit(7)\n')
        code, output, _ = run_staged_group("./scripts/group.sh", [Path("target.lp")], dict(os.environ))
        self.assertEqual(code, 7)
        self.assertIn("staged failure", output)
        saved = json.loads(next((self.root / "logs/check-runs").glob("*.json")).read_text())
        self.assertEqual(saved["kind"], "staged-check")
        self.assertEqual(saved["targets"], ["target.lp"])
        self.assertFalse(saved["reusable"])

    def test_staged_recipe_rejects_zero_exit_fatal_output(self):
        script = self.root / "scripts/group.sh"
        script.write_text('#!/bin/sh\nexec bash scripts/lambdapi_resource_guard.sh lambdapi check target.lp\n')
        script.chmod(0o755)
        self.checker('print("Uncaught [Out of memory].")\n')
        code, output, _ = run_staged_group("./scripts/group.sh", [Path("target.lp")], dict(os.environ))
        self.assertEqual(code, 1)
        self.assertIn("Uncaught [Out of memory].", output)
        saved = json.loads(next((self.root / "logs/check-runs").glob("*.json")).read_text())
        self.assertEqual(saved["recipeExit"], 0)
        self.assertEqual(saved["outcome"], "allocation-failed")
        self.assertFalse(saved["reusable"])


if __name__ == "__main__":
    unittest.main()
