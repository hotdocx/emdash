#!/usr/bin/env bash
# NON-LIBRARY whole x-family experiment in the strict reference environment.
# Source action on index arrows and generic lax profiles remain unqualified.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"
[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'native core changed; review the whole-family experiment\n' >&2; exit 2
}
[[ "$(git hash-object audits/total_op_reinterpretation.patch)" == 4d4c8a753bd0bfdada8a8e01eca2774d9c17c4c2 ]] || {
  printf 'preferred patch changed; review the whole-family experiment\n' >&2; exit 2
}
stage_root="$(mktemp -d /tmp/emdash-native-index-family.XXXXXX)"
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
    patches = ['total_op_reinterpretation.patch']
    if variant == 'candidate':
        patches.append('native_index_family_shift.patch')
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
    if 'homd_int' in strip_comments(prefix):
        raise SystemExit('prefix unexpectedly includes the native homd owner')
baseline = stage / 'baseline/emdash3_2.lp'
if hashlib.sha256(baseline.read_bytes()).hexdigest() != 'c120edf05f0ba89fa0a4dccee73a5e9f42232457397c15f061b9aa86c427255c':
    raise SystemExit('preferred baseline prefix changed')
files = ['native_homd_index_prototype.lp', 'native_index_family_prototype.lp',
         'native_index_source_arrow_observation.lp']
for file in files:
    shutil.copyfile(root / 'audits' / file, stage / 'candidate' / file)
(stage / 'logs').mkdir()
paths = [baseline, stage / 'candidate/emdash3_2.lp',
         stage / 'candidate/full_kernel_candidate.lp',
         *[stage / 'candidate' / file for file in files]]
manifest = {
    'scope': 'strict-reference whole x-family on an owning-position prefix',
    'fullKernelChecked': False,
    'genericLaxProfileQualified': False,
    'sourceActionOnIndexArrowsComputes': False,
    'sha256': {str(path.relative_to(stage)): hashlib.sha256(path.read_bytes()).hexdigest()
               for path in paths},
}
(stage / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY
printf 'strict-reference whole-family experiment; full repair remains pending\n'
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
check_target candidate native_index_family_prototype.lp family
check_target candidate native_index_source_arrow_observation.lp arrow-boundary
for file in emdash3_2.lp native_homd_index_prototype.lp native_index_family_prototype.lp \
    native_index_source_arrow_observation.lp; do
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
names = ['baseline', 'candidate', 'family', 'arrow-boundary']
inventories = {name: warning_inventory((stage / f'logs/{name}.log').read_text().splitlines())
               for name in names}
before, after = inventories['baseline'], inventories['candidate']
# Reviewed new instances caused by the D>=3 identity/composition, commutation,
# involution and whole/capped projection rules. This is not a confluence proof.
expected = Counter({
    ('fapp1_fapp0', 'id'): 2, ('Op_cat', 'fapp1_fapp0'): 1,
    ('comp_fapp0', 'comp_fapp0'): 12, ('comp_fapp0', 'fapp1_fapp0'): 16,
    ('fapp1_fapp0', 'fapp1_fapp0'): 7, ('CoAbove3_func', 'CoAbove3_func'): 1,
    ('fapp0', 'fapp1_func'): 1, ('hom_postcomp_func', 'id'): 1,
    ('hom_postcomp_fapp0', 'id'): 3, ('fapp1_fapp0', 'hom_postcomp_fapp0'): 16,
    ('hom_precomp_along_func', 'id'): 1, ('hom_precomp_along_fapp0', 'id'): 2,
    ('hom_precomp_along_fapp1_fapp0', 'id'): 1, ('fapp0', 'sigma_Fst'): 2,
    ('fapp0', 'sigma_Snd'): 2, ('Hom_func', 'id'): 2, ('Hom_fapp0', 'id'): 2,
    ('id', 'tapp1_fapp0'): 1, ('Op_adjunction', 'Op_cat'): 2,
    ('Op_cat', 'unit_adj_transf'): 2, ('Op_cat', 'counit_adj_transf'): 2,
})
if (after.rule_families - before.rule_families != expected
        or before.rule_families - after.rule_families
        or after.categories - before.categories != Counter({'unjoinable critical pair': 79})
        or before.categories - after.categories or after.parser_issues):
    raise SystemExit('warning delta changed; review the complete owning-position stream')
for name in ['family', 'arrow-boundary']:
    if inventories[name] != after:
        raise SystemExit(f'{name} changes the complete candidate warning inventory')
lines = (stage / 'logs/arrow-boundary.log').read_text().splitlines()
normal = [line for line in lines if line.startswith('λ Z:Cat,')]
if (len(normal) != 1 or '@sigma_map_func' not in normal[0]
        or '@hom_int_precomp_func' not in normal[0] or '@fapp1_fapp0' not in normal[0]):
    raise SystemExit('source-arrow computation boundary changed; inspect the normal form')
path = stage / 'manifest.json'
manifest = json.loads(path.read_text())
manifest.update(checksCompleted=True, wholeXFamilyTyped=True, sourcePointComputes=True,
                targetPrecompositionComputes=True, warningDeltaReviewed=79,
                warnings=dict(after.categories), lhsAudit='passed',
                arrowBoundary='Sigma map of opposite represented precomposition')
path.write_text(json.dumps(manifest, indent=2) + '\n')
print('reviewed +79 warning-family delta; complete reviewer inventories agree')
print('source-arrow action still stops at the recorded Sigma-map head')
PY
printf 'whole x-family experiment checks passed; active kernel unchanged\n'
