#!/usr/bin/env bash
# NON-LIBRARY direct native Homd candidate; the complete migration is pending.
# Checks the preserved Op source, first projections and fixed-(y,v) restriction.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"
[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'native core changed; review the direct Homd experiment\n' >&2; exit 2
}
stage_root="$(mktemp -d /tmp/emdash-homd-direct-owner.XXXXXX)"
printf 'retained sources and logs: %s\n' "$stage_root"
python3 - "$source_root" "$stage_root" <<'PY'
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from audit_rule_lhs import strip_comments
dest = stage / 'candidate'
dest.mkdir()
for file in ['emdash3_2.lp', 'lambdapi.pkg']:
    shutil.copyfile(root / file, dest / file)
patches = ['total_op_reinterpretation.patch', 'native_index_family_shift.patch',
           'hom_presheaf_transpose.patch', 'native_homd_direct_owner.patch']
for patch in patches:
    if patch == patches[-1]:
        preceding = (dest / 'emdash3_2.lp').read_text()
    with (dest / f'{patch}.log').open('w') as log:
        subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
                        str(root / 'audits' / patch)], cwd=dest,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
full = (dest / 'emdash3_2.lp').read_text()
if hashlib.sha256(full.encode()).hexdigest() != '401221ac2b5039341e65c184b3061645a978af209fc5d052036b6c22a9e61ee9':
    raise SystemExit('full candidate changed; review source and warning anchors')

def declaration(source, name):
    match = re.search(r'^(?:injective |constant )?symbol ' + name + r'\b', source, re.M)
    if not match:
        raise SystemExit(f'missing owner: {name}')
    return source[match.start():source.index(';', match.start()) + 1]

if declaration(full, 'homd_int') != declaration(preceding, 'homd_int'):
    raise SystemExit('the primitive homd_int declaration/source was changed')
for owner in ['Op_catd', 'Op_funcd', 'hom_int', 'homd_']:
    if declaration(full, owner) != declaration(preceding, owner):
        raise SystemExit(f'preserved owner changed: {owner}')

def unique_split(source, marker):
    if source.count(marker) != 1:
        raise SystemExit(f'source boundary changed: {marker}')
    return source.split(marker)

def focused_slice(source):
    prefix, _ = unique_split(source, '// Source y-component of the identity dependent-hom section.')
    at = source.index('injective symbol sigma_intro_transf ')
    sigma = source[at:source.index('// Generic Pi helper:', at)]
    start = '// 17b. Constant sections and delayed product-pair telescope rules'
    _, tail = unique_split(source, start)
    const, _ = unique_split(tail, '// Fibre component of a displayed constant transfor:')
    pair = '// Pairing telescope for products.'
    _, pairing = unique_split(tail, pair)
    pairing, _ = unique_split(pairing, '// 17c. Ordinary functor structural logic')
    start_full = '// Generic full hom-action for identity and composition of ordinary functors.'
    at = source.index(start_full)
    end = source.index(';', source.index(';', at) + 1) + 1
    return (prefix + '\n// Later independent owner dependencies in source order.\n'
            + sigma + '\n' + start + const + pair + pairing
            + '\n' + source[at:end] + '\n')

# Compare the two local folds with the same corrected declarations and other
# existing rules. This baseline is not the old, ill-typed full target.
without_folds = full
for marker in ['// Native point observation after the local-inclusion constructor has reduced.',
               '// Whole native homd restriction along the existing Sigma fibre inclusion.']:
    at = without_folds.index(marker)
    end = without_folds.index(';', at) + 1
    without_folds = without_folds[:at] + without_folds[end:]
for variant, source in [('baseline', without_folds), ('candidate', full)]:
    folder = stage / variant
    folder.mkdir(exist_ok=True)
    shutil.copyfile(root / 'lambdapi.pkg', folder / 'lambdapi.pkg')
    (folder / 'full_kernel_candidate.lp').write_text(source)
    (folder / 'emdash3_2.lp').write_text(focused_slice(source))
reviewers = ['native_homd_direct_input_controls.lp', 'native_homd_direct_owner_controls.lp',
             'native_homd_direct_expanded_hom_review.lp']
for file in reviewers:
    shutil.copyfile(root / 'audits' / file, dest / file)
    if re.search(r'\b(?:rule|unif_rule)\b', strip_comments((dest / file).read_text())):
        raise SystemExit(f'reviewer installs a rule: {file}')
(stage / 'logs').mkdir()
paths = [stage / variant / file for variant in ['baseline', 'candidate']
         for file in ['full_kernel_candidate.lp', 'emdash3_2.lp']]
paths += [dest / file for file in reviewers]
manifest = {
    'scope': 'native Op-source target, source projections and fixed-y-v whole restriction',
    'fullKernelAccepted': False,
    'primitiveHomdDeclarationPreserved': True,
    'pointwiseOpFamilyAndMapPreserved': True,
    'newPrimitives': 0,
    'newLocalRewriteRules': 2,
    'newUnificationRules': 0,
    'oldYSectionProjectionSuspended': True,
    'wholeVRestrictionQualified': False,
    'expandedHomProjectionOrderJoined': False,
    'genericLaxProfileQualified': False,
    'sha256': {str(path.relative_to(stage)): hashlib.sha256(path.read_bytes()).hexdigest()
               for path in paths},
}
(stage / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY

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
check_target candidate native_homd_direct_input_controls.lp inputs
check_target candidate native_homd_direct_owner_controls.lp owners
check_target candidate native_homd_direct_expanded_hom_review.lp expanded-hom
for variant in baseline candidate; do
  python3 scripts/audit_rule_lhs.py "$stage_root/$variant/emdash3_2.lp" --strict \
    >"$stage_root/logs/$variant.lhs.txt"
done
for file in native_homd_direct_input_controls.lp native_homd_direct_owner_controls.lp \
    native_homd_direct_expanded_hom_review.lp; do
  python3 scripts/audit_rule_lhs.py "$stage_root/candidate/$file" --strict \
    >"$stage_root/logs/$file.lhs.txt"
done

# One bounded check of the affected full owner locates the next unmigrated
# consumer. A timeout, signal, syntax error or different failure is not accepted.
set +e
(cd "$stage_root/candidate" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
  lambdapi check --no-colors full_kernel_candidate.lp) >"$stage_root/logs/full-boundary.log" 2>&1
boundary_status=$?
set -e
[[ "$boundary_status" == 1 ]] || {
  printf 'full-source outcome changed (%s); review its boundary log\n' "$boundary_status" >&2; exit 1
}
python3 - "$source_root" "$stage_root" <<'PY'
from collections import Counter
from difflib import SequenceMatcher
from pathlib import Path
import json
import sys

root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from warning_summary import warning_inventory
names = ['baseline', 'candidate', 'inputs', 'owners', 'expanded-hom']
inventories = {name: warning_inventory((stage / f'logs/{name}.log').read_text().splitlines())
               for name in names}
before, after = inventories['baseline'], inventories['candidate']
for field in ['categories', 'term_heads', 'rule_families', 'parser_issues']:
    if getattr(before, field) != getattr(after, field):
        raise SystemExit(f'local-fold warning {field} delta changed')
if after.parser_issues:
    raise SystemExit('unclassified warning stream')
if after.categories != Counter({'replaceable pattern variable': 139,
                                'unjoinable critical pair': 1101}):
    raise SystemExit('reviewed warning inventory changed')
line_map = {}
old = (stage / 'baseline/emdash3_2.lp').read_text().splitlines()
new = (stage / 'candidate/emdash3_2.lp').read_text().splitlines()
for block in SequenceMatcher(None, old, new, autojunk=False).get_matching_blocks():
    for offset in range(block.size):
        line_map[block.b + offset + 1] = block.a + offset + 1

def locations(inventory, mapping=None):
    result = Counter()
    for location, count in inventory.locations.items():
        file, line = location.rsplit(':', 1)
        line = int(line)
        if mapping is not None:
            if line not in mapping:
                raise SystemExit(f'warning in a new local fold: {location}')
            line = mapping[line]
        result[f'{Path(file).name}:{line}'] += count
    return result

if locations(before) != locations(after, line_map):
    raise SystemExit('warning locations changed beyond unchanged source-line mapping')
for name in names[2:]:
    if inventories[name] != after:
        raise SystemExit(f'{name} changes the complete candidate warning inventory')
source = (stage / 'candidate/full_kernel_candidate.lp').read_text()
at = source.index('symbol homd_id_tgt_func ')
line = source[:at].count('\n') + 1
failure = (stage / 'logs/full-boundary.log').read_text()
if (f'[full_kernel_candidate.lp:{line}:' not in failure
        or 'Some metavariables could not be solved' not in failure
        or 'Obj K ≡ Obj (@Sigma_cat' not in failure):
    raise SystemExit('full-source failure moved; review the actual native consumer')
normal = [line for line in (stage / 'logs/expanded-hom.log').read_text().splitlines()
          if line.startswith('λ ')]
path = stage / 'manifest.json'
manifest = json.loads(path.read_text())
manifest.update(checksCompleted=True, nativeSourceAndRestrictionChecks=True,
                displayedHomSourceComponentChecks=True, warningDeltaFromLocalFolds=0,
                warningLocationsMapped=True,
                warnings=dict(after.categories), lhsAudit='passed',
                firstUnmigratedOwner='homd_id_tgt_func', fullKernelAttempted=True,
                expandedHomObservedNormalForms=normal)
path.write_text(json.dumps(manifest, indent=2) + '\n')
print('local-fold warning inventories agree:', dict(after.categories))
print('full candidate reaches the old homd_id_tgt_func y-only evaluation')
PY
printf 'direct native owner checks passed; whole-v and higher-order joins remain pending\n'
