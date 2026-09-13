#!/usr/bin/env bash
# NON-LIBRARY structural source-arrow and source-2-cell computation.
# Full-kernel and generic-profile qualification remain separate gates.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"
[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'native core changed; review the structural Sigma experiment\n' >&2
  exit 2
}
[[ "$(git hash-object audits/total_op_reinterpretation.patch)" == 4d4c8a753bd0bfdada8a8e01eca2774d9c17c4c2 ]] || {
  printf 'preferred patch changed; review the structural Sigma experiment\n' >&2
  exit 2
}
stage_root="$(mktemp -d /tmp/emdash-native-sigma-precomp.XXXXXX)"
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
for variant in ['baseline', 'candidate']:
    dest = stage / variant
    dest.mkdir()
    for file in ['emdash3_2.lp', 'lambdapi.pkg']:
        shutil.copyfile(root / file, dest / file)
    patches = ['total_op_reinterpretation.patch', 'native_index_family_shift.patch']
    if variant == 'candidate':
        patches.append('native_sigma_precomp.patch')
    for patch in patches:
        with (dest / f'{patch}.log').open('w') as log:
            subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
                            str(root / 'audits' / patch)], cwd=dest,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    full = (dest / 'emdash3_2.lp').read_text()
    marker = '// 12. Directed homd target and internal homd functor'
    if full.count(marker) != 1:
        raise SystemExit('native target marker changed')
    (dest / 'full_kernel_candidate.lp').write_text(full)
    prefix = full.split(marker)[0]
    (dest / 'emdash3_2.lp').write_text(prefix)
    code = strip_comments(prefix)
    for owner in ['homd_int', 'fdapp1_int_cell', 'tdapp1_int_func_transfd']:
        if owner in code:
            raise SystemExit(f'prefix unexpectedly depends on {owner}')
baseline = stage / 'baseline/emdash3_2.lp'
if hashlib.sha256(baseline.read_bytes()).hexdigest() != '6b779ee8080e2eabbe290b4d8c9ff49f668c28f38492e4f103849d1c99df0d13':
    raise SystemExit('whole-family baseline prefix changed')
files = ['native_homd_index_prototype.lp', 'native_index_family_prototype.lp',
         'native_sigma_precomp_controls.lp', 'native_index_source_two_cell_observation.lp',
         'native_sigma_source_two_cell_controls.lp']
for file in files:
    shutil.copyfile(root / 'audits' / file, stage / 'candidate' / file)
(stage / 'logs').mkdir()
paths = [baseline, stage / 'candidate/emdash3_2.lp',
         stage / 'candidate/full_kernel_candidate.lp',
         *[stage / 'candidate' / file for file in files]]
manifest = {
    'scope': 'strict-reference structural index source action before native homd',
    'fullKernelChecked': False,
    'genericLaxProfileQualified': False,
    'checksCompleted': False,
    'sha256': {str(path.relative_to(stage)): hashlib.sha256(path.read_bytes()).hexdigest()
               for path in paths},
}
(stage / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY
printf 'structural Sigma source-action experiment; full repair remains pending\n'
printf 'retained sources and logs: %s\n' "$stage_root"
check_target() {
  local variant="$1" file="$2" label="$3"
  printf 'checking %s/%s with the repository resource guard\n' "$variant" "$file"
  if ! (cd "$stage_root/$variant" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
      lambdapi check --no-colors "$file") >"$stage_root/logs/$label.log" 2>&1; then
    python3 scripts/explain_failure.py "$stage_root/logs/$label.log" || true
    exit 1
  fi
}
check_target baseline emdash3_2.lp baseline
check_target candidate emdash3_2.lp candidate
check_target candidate native_sigma_precomp_controls.lp arrows
check_target candidate native_sigma_source_two_cell_controls.lp source-two-cells
for file in emdash3_2.lp native_sigma_precomp_controls.lp \
    native_index_source_two_cell_observation.lp native_sigma_source_two_cell_controls.lp; do
  python3 scripts/audit_rule_lhs.py "$stage_root/candidate/$file" --strict \
    >"$stage_root/logs/$file.lhs.txt"
done
python3 - "$source_root" "$stage_root" <<'PY'
from collections import Counter
from pathlib import Path
import json
import sys
root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from warning_summary import warning_inventory
names = ['baseline', 'candidate', 'arrows', 'source-two-cells']
inventories = {name: warning_inventory((stage / f'logs/{name}.log').read_text().splitlines())
               for name in names}
before, after = inventories['baseline'], inventories['candidate']
expected = Counter({('fapp0', 'fapp1_func'): 1,
                    ('comp_fapp0', 'fapp1_func'): 1,
                    ('fapp1_fapp0', 'tapp0_hom_fapp0'): 6,
                    ('CoAbove2_cat', 'tapp0_hom_fapp0'): 1})
if (after.rule_families - before.rule_families != expected
        or before.rule_families - after.rule_families
        or after.categories - before.categories != Counter({'unjoinable critical pair': 9})
        or before.categories - after.categories or after.parser_issues):
    raise SystemExit('warning delta changed; review the owning-position stream')
for name in ['arrows', 'source-two-cells']:
    if inventories[name] != after:
        raise SystemExit(f'{name} changes the complete candidate warning inventory')
normal = [line for line in (stage / 'logs/source-two-cells.log').read_text().splitlines()
          if line.startswith('λ Z:Cat,')]
if (len(normal) != 1 or '@Struct_sigma' not in normal[0]
        or '@comp_prod_fapp1_fapp0' not in normal[0]
        or '@tapp0_hom_fapp0' in normal[0] or '@sigma_map_transf' in normal[0]):
    raise SystemExit('source-2-cell normal form changed; inspect the actual component')
path = stage / 'manifest.json'
manifest = json.loads(path.read_text())
manifest.update(checksCompleted=True, stableAndRawArrowBeta=True,
                sourceTwoCellBeta=True, changedDataAndDirectionNegatives=True,
                sideConditionDoesNotInventFactorization=True,
                warningDeltaReviewed=9, warnings=dict(after.categories), lhsAudit='passed')
path.write_text(json.dumps(manifest, indent=2) + '\n')
print('complete arrow/2-cell checks pass; reviewer warning inventories agree')
print('reviewed +9 prefix warning-family delta; full-kernel joins remain unqualified')
PY
printf 'structural Sigma source-action checks passed; active kernel unchanged\n'
