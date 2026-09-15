"""Check the bounded native-pair profile without invoking a large checker."""
import importlib.util
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
spec = importlib.util.spec_from_file_location('pair_metrics', SCRIPTS / 'check_metrics.py')
metrics = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = metrics
spec.loader.exec_module(metrics)

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
            self.assertEqual(metrics.lambdapi_check_command(Path('unrelated.lp')),['lambdapi','check','-w','unrelated.lp'])

    def test_resume_rejects_memory_deadline_or_guard_changes(self):
        root=Path(self.temp.name)
        with patch.object(metrics,'ROOT',root), patch.dict(os.environ,{},clear=True):
            before=metrics.check_state_identity([], 'source', 'version', '90s')
            for change in [{'EMDASH_LP_MEMORY_MIB':'6144'}, {'EMDASH_PROBE_TIMEOUT':'180s'}]:
                with patch.dict(os.environ,change):
                    after=metrics.check_state_identity([], 'source', 'version', '90s')
                self.assertFalse(metrics.resume_identity_is_compatible(before,after,root))
            guard=root/'scripts/lambdapi_resource_guard.sh'
            guard.write_text(guard.read_text()+'\n# profile changed\n')
            after=metrics.check_state_identity([], 'source', 'version', '90s')
            self.assertFalse(metrics.resume_identity_is_compatible(before,after,root))

if __name__=='__main__':unittest.main()
