"""Check the bounded native-pair profile without invoking a large checker."""
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

class PairProfileTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='emdash-pair-profile-')
        self.addCleanup(self.temp.cleanup)
        scripts = Path(self.temp.name) / 'scripts'
        scripts.mkdir()
        self.runner = scripts / 'check_native_snake_pairs.sh'
        shutil.copyfile(SCRIPTS / self.runner.name, self.runner)
        for name in ["check_native_snake_six_term.sh", "lambdapi_resource_guard.sh"]:
            shutil.copyfile(SCRIPTS / name, scripts / name)
        stub = scripts / 'probe.sh'
        stub.write_text('#!/usr/bin/env python3\nimport os,json,sys\nprint(json.dumps({"target":sys.argv[1],"memory":os.environ["EMDASH_LP_MEMORY_MIB"],"timeout":os.environ["EMDASH_PROBE_TIMEOUT"],"gc":os.environ["OCAMLRUNPARAM"]}))\n')
        stub.chmod(0o755)
        self.env = {k:v for k,v in os.environ.items() if k not in {'EMDASH_LP_MEMORY_MIB','EMDASH_PROBE_TIMEOUT','OCAMLRUNPARAM'}}
        # A minimal source fixture exercises the real registry-backed wrapper.
        for name in ["check_profile.py", "check_registry.py"]:
            shutil.copyfile(SCRIPTS / name, scripts / name)
        registry = json.loads((SCRIPTS.parent / "checks.json").read_text())
        names = sorted({path for targets in registry["profileTargets"].values() for path in targets})
        registry.update(core=[name for name in names if not name.startswith("examples/")],
                        reviewers=[name for name in names if name.startswith("examples/")],
                        check=[], priority=[], isolatedGroups=[])
        (scripts.parent / "checks.json").write_text(json.dumps(registry))
        for name in names:
            source = scripts.parent / name
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("symbol fixture : TYPE;\n")

    def run_profile(self, *args, **env):
        return subprocess.run(['bash',str(self.runner),*args],env={**self.env,**env},text=True,capture_output=True,timeout=5)
    def test_exact_registered_set_and_limits(self):
        r=self.run_profile();self.assertEqual(r.returncode,0,r.stderr)
        rows=[json.loads(x) for x in r.stdout.splitlines()]
        self.assertEqual({Path(x['target']) for x in rows},metrics.NATIVE_SNAKE_PAIR_CHECK_FILES)
        self.assertTrue(all(x['memory']=='6144' and x['timeout']=='180s' and x['gc']=='o=20' for x in rows))
    def test_explicit_bounded_overrides_are_retained(self):
        target=sorted(map(str,metrics.NATIVE_SNAKE_PAIR_CHECK_FILES))[0]
        r=self.run_profile(target,EMDASH_LP_MEMORY_MIB='4096',EMDASH_PROBE_TIMEOUT='120s',OCAMLRUNPARAM='o=10')
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertEqual(json.loads(r.stdout),{'target':target,'memory':'4096','timeout':'120s','gc':'o=10'})
    def test_unknown_target_is_rejected(self):
        r=self.run_profile('unrelated.lp');self.assertEqual(r.returncode,2);self.assertEqual(r.stdout,'')
    def test_only_named_targets_use_the_profile(self):
        with patch.dict(os.environ,{},clear=True):
            for p in metrics.NATIVE_SNAKE_PAIR_CHECK_FILES:
                self.assertEqual(metrics.lambdapi_check_command(p),['./scripts/check_native_snake_pairs.sh',str(p)])
            self.assertEqual(metrics.lambdapi_check_command(Path('unrelated.lp')),[sys.executable,'./scripts/run_lambdapi.py','--quiet','unrelated.lp'])

    def test_resume_rejects_memory_deadline_or_guard_changes(self):
        root=Path(self.temp.name)
        with patch.object(metrics,'ROOT',root), patch.dict(os.environ,{},clear=True), patch.object(metrics.shutil, 'which', return_value=sys.executable):
            before=metrics.check_state_identity([], 'source', 'version', '90s')
            self.assertTrue(metrics.resume_identity_is_compatible(before, before, root))
            for change in [{'EMDASH_LP_MEMORY_MIB':'6144'}, {'EMDASH_PROBE_TIMEOUT':'180s'}]:
                with patch.dict(os.environ,change):
                    after=metrics.check_state_identity([], 'source', 'version', '90s')
                self.assertFalse(metrics.resume_identity_is_compatible(before,after,root))
            guard=root/'scripts/lambdapi_resource_guard.sh'
            guard.write_text(guard.read_text()+'\n# profile changed\n')
            after=metrics.check_state_identity([], 'source', 'version', '90s')
            self.assertFalse(metrics.resume_identity_is_compatible(before,after,root))

if __name__=='__main__':unittest.main()
