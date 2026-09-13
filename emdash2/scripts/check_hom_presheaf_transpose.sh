#!/usr/bin/env bash
# NON-LIBRARY: repair the existing defined HomPresheaf in a copied owner slice.
# Full Homd integration and the source-2-cell component formula remain pending.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"
[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'native core changed; review the HomPresheaf experiment\n' >&2; exit 2
}
[[ "$(git hash-object audits/total_op_reinterpretation.patch)" == 4d4c8a753bd0bfdada8a8e01eca2774d9c17c4c2 ]] || {
  printf 'preferred patch changed; review the HomPresheaf experiment\n' >&2; exit 2
}
stage_root="$(mktemp -d /tmp/emdash-hom-presheaf-transpose.XXXXXX)"
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

expected = {
    'baseline/full_kernel_candidate.lp': '238f06f65672aa1c49bc9b4afb817023a627dba1493a8c012ee23e26f3a08cd4',
    'candidate/full_kernel_candidate.lp': '95c8898dd8b87f4122c2860acd1c089e0810f8e6ccb7f8ca4d896ce7d25284ea',
    'baseline/emdash3_2.lp': '8618d4b28911142277455fd84b20df883d374662d17c2e9cc40c3c9931377357',
    'candidate/emdash3_2.lp': '910b2c9cf0609b14be233cb5275e87058bbe14066ffcc680815480f5aac4fcf3',
}

def unique_split(text, marker):
    if text.count(marker) != 1:
        raise SystemExit(f'source marker changed: {marker}')
    return text.split(marker)

def focused_slice(full):
    prefix, _ = unique_split(full, '// 12. Directed homd target and internal homd functor')
    start = '// 17b. Constant sections and delayed product-pair telescope rules'
    _, tail = unique_split(full, start)
    const, _ = unique_split(tail, '// Fibre component of a displayed constant transfor:')
    pair = '// Pairing telescope for products.'
    _, pairing = unique_split(tail, pair)
    pairing, _ = unique_split(pairing, '// 17c. Ordinary functor structural logic')
    support = ('\n// Unchanged later dependencies retained in original source order for this focused slice.\n'
               + start + const + pair + pairing)
    start = '// Generic full hom-action for identity and composition of ordinary functors.'
    _, tail = unique_split(full, start)
    second = tail.index(';', tail.index(';') + 1)
    block = start + tail[:second + 1] + '\n'
    if block.count('\nrule ') != 2:
        raise SystemExit('full-action dependency boundary changed')
    support += ('\n// Unchanged later full-action dependency, after the preceding section dependencies.\n'
                + block)
    return prefix + support

full_sources = {}
for variant in ['baseline', 'candidate']:
    dest = stage / variant
    dest.mkdir()
    for file in ['emdash3_2.lp', 'lambdapi.pkg']:
        shutil.copyfile(root / file, dest / file)
    patches = ['total_op_reinterpretation.patch', 'native_index_family_shift.patch']
    if variant == 'candidate':
        patches.append('hom_presheaf_transpose.patch')
    for patch in patches:
        with (dest / f'{patch}.log').open('w') as log:
            subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
                            str(root / 'audits' / patch)], cwd=dest,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    full = (dest / 'emdash3_2.lp').read_text()
    full_sources[variant] = full
    (dest / 'full_kernel_candidate.lp').write_text(full)
    (dest / 'emdash3_2.lp').write_text(focused_slice(full))

# The full-file change is confined to defined terms at the existing owner.
# In particular, later dependencies are not relocated in the full source.
regions = {}
for variant, marker in [
    ('baseline', '// Internalized classifier: hom-presheaf family for a represented object.'),
    ('candidate', '// Candidate source definitions for the existing HomPresheaf owner.'),
]:
    before, tail = unique_split(full_sources[variant], marker)
    end = tail.index(';', tail.index('symbol HomPresheaf_catd_func')) + 1
    regions[variant] = (before, tail[:end], tail[end:])

def code(text):
    return ' '.join(strip_comments(text).split())

for index in [0, 2]:
    if code(regions['baseline'][index]) != code(regions['candidate'][index]):
        raise SystemExit('change escaped the existing defined HomPresheaf owner')
helpers = ['native_transpose_universe', 'native_shift_product_intro',
           'native_presheaf_universe', 'native_hom_presheaf_bifunctor']
for variant, names in [('baseline', ['HomPresheaf_catd_func']),
                       ('candidate', helpers + ['HomPresheaf_catd_func'])]:
    body = strip_comments(regions[variant][1])
    if re.findall(r'\bsymbol\s+(\w+)', body) != names:
        raise SystemExit(f'{variant} defined-owner inventory changed')
    statements = [part.strip() for part in body.split(';') if part.strip()]
    if len(statements) != len(names) or any(
        not part.startswith('symbol ') or '≔' not in part for part in statements
    ) or re.search(r'\b(?:rule|unif_rule)\b', body):
        raise SystemExit('a primitive or rule was introduced in the definition slice')

for file, digest in expected.items():
    if hashlib.sha256((stage / file).read_bytes()).hexdigest() != digest:
        raise SystemExit(f'copied source changed; review {file}')
reviewers = ['hom_presheaf_transpose_controls.lp',
             'hom_presheaf_transpose_action_controls.lp',
             'hom_presheaf_transpose_two_cell_review.lp']
for file in reviewers:
    shutil.copyfile(root / 'audits' / file, stage / 'candidate' / file)
    if re.search(r'\b(?:rule|unif_rule)\b', strip_comments((stage / 'candidate' / file).read_text())):
        raise SystemExit(f'reviewer installs a rule: {file}')
(stage / 'logs').mkdir()
paths = [stage / file for file in expected] + [stage / 'candidate' / file for file in reviewers]
manifest = {
    'scope': 'defined HomPresheaf owner with unchanged later dependencies in source order',
    'fullKernelChecked': False,
    'genericLaxProfileQualified': False,
    'newPrimitives': 0,
    'addedRewriteRules': 0,
    'addedUnificationRules': 0,
    'relocatedExistingRules': 0,
    'helperDefinitions': helpers,
    'changedDefinedOwner': 'HomPresheaf_catd_func',
    'sourceTwoCellComponentFormulaVerified': False,
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
check_target candidate hom_presheaf_transpose_controls.lp points
check_target candidate hom_presheaf_transpose_action_controls.lp actions
check_target candidate hom_presheaf_transpose_two_cell_review.lp two-cell
for variant in baseline candidate; do
  python3 scripts/audit_rule_lhs.py "$stage_root/$variant/emdash3_2.lp" --strict \
    >"$stage_root/logs/$variant.lhs.txt"
done
for file in hom_presheaf_transpose_controls.lp hom_presheaf_transpose_action_controls.lp \
    hom_presheaf_transpose_two_cell_review.lp; do
  python3 scripts/audit_rule_lhs.py "$stage_root/candidate/$file" --strict \
    >"$stage_root/logs/$file.lhs.txt"
done
python3 - "$source_root" "$stage_root" <<'PY'
from collections import Counter
from difflib import SequenceMatcher
from pathlib import Path
import json
import sys

root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from warning_summary import warning_inventory

names = ['baseline', 'candidate', 'points', 'actions', 'two-cell']
inventories = {name: warning_inventory((stage / f'logs/{name}.log').read_text().splitlines())
               for name in names}
before, after = inventories['baseline'], inventories['candidate']
for field in ['categories', 'term_heads', 'rule_families', 'parser_issues']:
    if getattr(before, field) != getattr(after, field):
        raise SystemExit(f'warning {field} changed; review the source interaction')
if after.parser_issues:
    raise SystemExit('unclassified warning stream')

# Match warning locations through exact unchanged source lines, not a blanket
# numeric offset that might hide a new warning inside the changed definition.
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
                raise SystemExit(f'warning in changed source: {location}')
            line = mapping[line]
        result[f'{Path(file).name}:{line}'] += count
    return result

if locations(before) != locations(after, line_map):
    raise SystemExit('warning locations changed beyond unchanged source-line mapping')
for name in names[2:]:
    if inventories[name] != after:
        raise SystemExit(f'{name} changes the complete candidate warning inventory')
normal_forms = [line for line in (stage / 'logs/two-cell.log').read_text().splitlines()
                if line.startswith('λ ')]
path = stage / 'manifest.json'
manifest = json.loads(path.read_text())
manifest.update(checksCompleted=True, pointAndNativeEndpointChecks=True,
                sourceAndTargetArrowChecks=True, sourceTwoCellTyped=True,
                warningDelta=0, warningLocationsMapped=True,
                warnings=dict(after.categories), lhsAudit='passed',
                sourceTwoCellObservedNormalForms=normal_forms)
path.write_text(json.dumps(manifest, indent=2) + '\n')
print('complete warning inventories agree after exact source-line mapping')
print(json.dumps(dict(after.categories)))
PY
printf 'HomPresheaf point/arrow checks passed; higher component and full Homd remain pending\n'
