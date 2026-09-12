#!/usr/bin/env bash
# NON-LIBRARY shared-index ingredient; the full native Homd target is pending.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"
[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'native core anchor changed; review this experiment first\n' >&2
  exit 2
}
[[ "$(git hash-object audits/total_op_reinterpretation.patch)" == 4d4c8a753bd0bfdada8a8e01eca2774d9c17c4c2 ]] || {
  printf 'preferred-duality patch changed; review this experiment first\n' >&2
  exit 2
}
stage_root="$(mktemp -d /tmp/emdash-native-homd-index.XXXXXX)"
python3 - "$source_root" "$stage_root" <<'PY'
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from audit_rule_lhs import strip_comments
for file in ['emdash3_2.lp', 'lambdapi.pkg']:
    shutil.copyfile(root / file, stage / file)
(stage / 'logs').mkdir()
with (stage / 'logs/patch.log').open('w') as log:
    subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
                    str(root / 'audits/total_op_reinterpretation.patch')],
                   cwd=stage, stdout=log, stderr=subprocess.STDOUT, check=True)
full = (stage / 'emdash3_2.lp').read_text()
marker = '// 12. Directed homd target and internal homd functor'
if full.count(marker) != 1:
    raise SystemExit('native target marker changed')
(stage / 'full_kernel_candidate.lp').write_text(full)
prefix = full.split(marker)[0]
if hashlib.sha256(prefix.encode()).hexdigest() != 'c120edf05f0ba89fa0a4dccee73a5e9f42232457397c15f061b9aa86c427255c':
    raise SystemExit('preferred source prefix changed; review required')
(stage / 'emdash3_2.lp').write_text(prefix)
code = strip_comments(prefix)
for owner in ['homd_int', 'fdapp1_int_cell', 'tdapp1_int_func_transfd']:
    if owner in code:
        raise SystemExit(f'prefix unexpectedly depends on {owner}')
reviewer = root / 'audits/native_homd_index_prototype.lp'
shutil.copyfile(reviewer, stage / reviewer.name)
reviewer_code = strip_comments(reviewer.read_text())
for owner in ['sigma_map_func', 'homd_int', 'fdapp1_int_cell', 'tdapp1_int_func_transfd']:
    if owner in reviewer_code:
        raise SystemExit(f'index prototype unexpectedly uses {owner}')
names = ['emdash3_2.lp', reviewer.name, 'full_kernel_candidate.lp']
manifest = {
    'scope': 'native index carrier, constructor/projection and source-Hom direction on the preferred prefix',
    'fullKernelChecked': False,
    'wholeXFamilyChecked': False,
    'genericLaxProfileQualified': False,
    'nativeHomdOwnerAbsentFromPrefix': True,
    'sha256': {name: hashlib.sha256((stage / name).read_bytes()).hexdigest() for name in names},
}
(stage / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY
printf 'shared-index ingredient only; full target and generic profiles remain pending\n'
printf 'retained sources and logs: %s\n' "$stage_root"
for file in emdash3_2.lp native_homd_index_prototype.lp; do
  log="$stage_root/logs/$file.log"
  printf 'checking %s with the repository resource guard\n' "$file"
  if ! (cd "$stage_root" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
      lambdapi check --no-colors "$file") >"$log" 2>&1; then
    python3 scripts/explain_failure.py "$log" || true
    exit 1
  fi
  python3 scripts/audit_rule_lhs.py "$stage_root/$file" --strict \
    >"$stage_root/logs/$file.lhs.txt"
done
python3 - "$source_root" "$stage_root" <<'PY'
from pathlib import Path
import json
import sys
root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from warning_summary import warning_inventory
inventories = [warning_inventory((stage / f'logs/{name}.log').read_text().splitlines())
               for name in ['emdash3_2.lp', 'native_homd_index_prototype.lp']]
if inventories[0] != inventories[1] or inventories[0].parser_issues:
    raise SystemExit('reviewer warning inventory differs from its exact prefix')
path = stage / 'manifest.json'
manifest = json.loads(path.read_text())
manifest.update(checksCompleted=True, warningInventoriesAgree=True,
                warnings=dict(inventories[0].categories), lhsAudit='passed')
path.write_text(json.dumps(manifest, indent=2) + '\n')
print('complete warning inventories agree; strict LHS audits pass')
PY
printf 'native shared-index ingredient checks passed; active kernel unchanged\n'
