"""Scoped runner/profile checks; no checker or large allocation is needed."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parent
if __package__:
    from . import check_metrics as metrics
else:
    import check_metrics as metrics


class NativeGcProfileTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="emdash-gc-profile-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        self.runner = scripts / "check_native_snake_six_term.sh"
        shutil.copyfile(SCRIPTS / self.runner.name, self.runner)
        shutil.copyfile(SCRIPTS / "check_native_snake_pairs.sh", scripts / "check_native_snake_pairs.sh")
        shutil.copyfile(SCRIPTS / "lambdapi_resource_guard.sh", scripts / "lambdapi_resource_guard.sh")
        stub = scripts / "probe.sh"
        stub.write_text("#!/usr/bin/env python3\nimport json,os,sys\nprint(json.dumps({'args':sys.argv[1:],'gc':os.environ.get('OCAMLRUNPARAM')}))\n")
        stub.chmod(0o755)
        self.env = {k: v for k, v in os.environ.items() if k not in {"OCAMLRUNPARAM", "CAMLRUNPARAM"}}

        # A minimal source fixture exercises the real registry-backed wrapper.
        for name in ["check_profile.py", "check_registry.py"]:
            shutil.copyfile(SCRIPTS / name, scripts / name)
        registry = json.loads((SCRIPTS.parent / "checks.json").read_text())
        names = sorted({path for targets in registry["profileTargets"].values() for path in targets}
                       | set(registry.get("targetProfileOverrides", {})))
        registry.update(core=[name for name in names if not name.startswith("examples/")],
                        reviewers=[name for name in names if name.startswith("examples/")],
                        check=[], priority=[], isolatedGroups=[])
        (scripts.parent / "checks.json").write_text(json.dumps(registry))
        for name in names:
            source = scripts.parent / name
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("symbol fixture : TYPE;\n")

    def run_profile(self, *args, gc=None):
        env = dict(self.env)
        if gc is not None:
            env["OCAMLRUNPARAM"] = gc
        return subprocess.run(["bash", str(self.runner), *args], env=env,
                              capture_output=True, text=True, timeout=5)

    def test_default_checks_exact_target_set(self):
        result = self.run_profile()
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        self.assertEqual({Path(row["args"][0]) for row in rows}, metrics.NATIVE_SIX_TERM_GC_CHECK_FILES)
        self.assertEqual(len(rows), 8)
        measured_overrides = {
            "emdash3_2_one_cat_native_snake_six_term_result.lp",
            "examples/one_cat_native_snake_six_term_data.lp",
            "examples/one_cat_native_snake_six_term_inputs.lp",
            "examples/one_cat_native_snake_six_term_result.lp",
        }
        for row in rows:
            expected = "o=20,v=1024" if row["args"][0] in measured_overrides else "o=20"
            self.assertEqual(row["gc"], expected)

    def test_selected_target_and_explicit_profile(self):
        target = "examples/one_cat_native_snake_six_term_inputs.lp"
        result = self.run_profile(target, gc="o=10,v=1024")
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        self.assertEqual(rows, [{"args": [target], "gc": "o=10,v=1024"}])

    def test_unregistered_target_is_rejected_before_probe(self):
        result = self.run_profile("unrelated.lp")
        self.assertEqual(result.returncode, 2)
        self.assertNotIn('"args"', result.stdout)

    def test_metrics_routes_only_registered_profile_targets(self):
        with patch.dict(os.environ, {}, clear=True):
            for target in metrics.NATIVE_SIX_TERM_GC_CHECK_FILES:
                self.assertEqual(metrics.lambdapi_check_command(target),
                                 ["./scripts/check_native_snake_six_term.sh", str(target)])
            self.assertEqual(metrics.lambdapi_check_command(Path("unrelated.lp")),
                             [sys.executable, "./scripts/run_lambdapi.py", "--quiet", "unrelated.lp"])

    def test_resume_rejects_runtime_or_profile_script_changes(self):
        with patch.object(metrics, "ROOT", self.root), patch.dict(os.environ, {}, clear=True), patch.object(metrics.shutil, "which", return_value=sys.executable):
            before = metrics.check_state_identity([], "source", "version", "90s")
            self.assertTrue(metrics.resume_identity_is_compatible(before, before, self.root))
            self.assertEqual(before["ocamlrunparam"], "")
            with patch.dict(os.environ, {"OCAMLRUNPARAM": "o=10"}):
                changed = metrics.check_state_identity([], "source", "version", "90s")
            self.assertFalse(metrics.resume_identity_is_compatible(before, changed, self.root))
            self.runner.write_text(self.runner.read_text() + "\n# changed profile\n")
            changed = metrics.check_state_identity([], "source", "version", "90s")
            self.assertFalse(metrics.resume_identity_is_compatible(before, changed, self.root))


if __name__ == "__main__":
    unittest.main()
