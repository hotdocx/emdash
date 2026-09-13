#!/usr/bin/env bash
# NON-LIBRARY diagnostic: acceptance of an Empty witness reproduces a defect.
# The subtraction variants isolate causes; they are not a kernel repair.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"

[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'active source changed; review the family/section diagnostic\n' >&2
  exit 2
}
[[ "$(git hash-object audits/total_op_reinterpretation.patch)" == 4d4c8a753bd0bfdada8a8e01eca2774d9c17c4c2 ]] || {
  printf 'preferred duality patch changed; review this isolation\n' >&2
  exit 2
}
stage_root="$(mktemp -d /tmp/emdash-family-section-profile.XXXXXX)"

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

(stage / 'logs').mkdir()
for variant in ['active', 'preferred']:
    dest = stage / variant
    dest.mkdir()
    for name in ['emdash3_2.lp', 'lambdapi.pkg']:
        shutil.copyfile(root / name, dest / name)
with (stage / 'logs/patch.log').open('w') as log:
    subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
                    str(root / 'audits/total_op_reinterpretation.patch')],
                   cwd=stage / 'preferred', stdout=log,
                   stderr=subprocess.STDOUT, check=True)
full = (stage / 'preferred/emdash3_2.lp').read_text()
marker = '// Pointwise total opposite changes the base to CoAbove2(K).'
evaluation = '// Constant-family section evaluation follows ordinary functor application.'
if full.count(marker) != 1 or full.count(evaluation) != 1:
    raise SystemExit('source extraction anchors changed')
prefix = full.split(marker)[0]
# Copy the unchanged constant-section beta into its dependency-complete owner
# slice. No native homd/Sigma declaration or computation is copied with it.
prefix += '\n' + evaluation + full.split(evaluation)[1].split('// Final endpoint fold.')[0]
code = strip_comments(prefix)
if re.search(r'\bsymbol\s+(?:Sigma_cat|homd_int|homd_|Op_catd)\b', code):
    raise SystemExit('isolation unexpectedly contains a later family/Sigma/homd owner')
if 'constant symbol op : τ (Functor (CoAbove2_cat Cat_cat) Cat_cat);' not in code:
    raise SystemExit('preferred shifted op signature is missing')

object_marker = '// Cat-valued object-level projections of strict naturality.'
next_section = '// -------------------------------------------------------------------------------------------------\n// 7. Product functor packages'
left, rest = prefix.split(object_marker)
removed_objects, right = rest.split(next_section)
if removed_objects.count('\nrule ') != 2:
    raise SystemExit('object-cut subtraction changed')
without_objects = left + next_section + right
stable_marker = '/*\n  Proof-time stable-head readings of the two component cuts above.'
left, rest = without_objects.split(stable_marker)
removed_stable, right = rest.split(next_section)
if removed_stable.count('unif_rule') != 2 or '\nrule ' in removed_stable:
    raise SystemExit('stable-head subtraction changed')
without_endpoints = left + next_section + right
sources = {
    'cuts': prefix,
    'without_object_cuts': without_objects,
    'without_four_endpoint_cuts': without_endpoints,
}
expected = {
    'cuts': '8b23cbe9e5756d32ffde9b9989f4442714c28c843cceb9e0e92d6742cecf5503',
    'without_object_cuts': 'ab48b3bd9dddbc5bdb8bf2bc368a7ed909ef7d83b0d63ddecf1a42c016a3de9c',
    'without_four_endpoint_cuts': 'bad6c08f4b73d625fc199e53bd69f6d1dc156de1cbc94ffa8c0b39e78b8fa206',
}
for variant, source in sources.items():
    if hashlib.sha256(source.encode()).hexdigest() != expected[variant]:
        raise SystemExit(f'{variant}: source identity changed')
    dest = stage / variant
    dest.mkdir()
    (dest / 'emdash3_2.lp').write_text(source)
    shutil.copyfile(root / 'lambdapi.pkg', dest / 'lambdapi.pkg')

fixtures = [
    'family_section_strict_transport_empty_reproducer.lp',
    'family_section_object_cuts_empty_reproducer.lp',
    'family_section_stable_cuts_empty_reproducer.lp',
    'family_section_profile_controls.lp',
]
for variant in ['active', *sources]:
    for name in fixtures:
        source = root / 'audits' / name
        code = strip_comments(source.read_text())
        if re.search(r'\b(?:rule|unif_rule|constant|injective)\b', code):
            raise SystemExit(f'{name}: diagnostic is no longer rule-free')
        shutil.copyfile(source, stage / variant / name)
paths = [p for p in stage.rglob('*.lp')] + [stage / 'active/lambdapi.pkg']
manifest = {
    'scope': 'non-library family/section profile soundness diagnostic',
    'activeKernelModified': False,
    'fullPreferredKernelChecked': False,
    'profileRepairQualified': False,
    'checksCompleted': False,
    'sourceBlob': '91f1974ece225e399604dce24710bf1437ad3ef5',
    'sha256': {str(p.relative_to(stage)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in paths},
}
(stage / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY

printf 'NON-LIBRARY diagnostic; Empty acceptance reproduces a soundness defect\n'
printf 'retained sources and logs: %s\n' "$stage_root"
check_target() {
  local variant="$1" file="$2" label="$3"
  printf 'checking %s/%s\n' "$variant" "$file"
  if ! (cd "$stage_root/$variant" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
      lambdapi check --no-colors "$file") >"$stage_root/logs/$label.log" 2>&1; then
    python3 scripts/explain_failure.py "$stage_root/logs/$label.log" || true
    exit 1
  fi
}
reject_at_endpoint() {
  local variant="$1" file="$2" label="$3" route="$4" rc=0
  (cd "$stage_root/$variant" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
    lambdapi check -w --no-colors "$file") >"$stage_root/logs/$label.log" 2>&1 || rc=$?
  [[ "$rc" == 1 ]] || {
    printf '%s returned %s; expected the recorded type failure (1)\n' "$label" "$rc" >&2
    exit 1
  }
  python3 - "$stage_root/logs/$label.log" "$route" <<'PY'
from pathlib import Path
import re
import sys
text = Path(sys.argv[1]).read_text()
goals = re.findall(r'^\d+\. (.*)$', text, re.M)
expected_count = 2 if sys.argv[2] == 'object' else 1
if ('The proof is not finished:' not in text or len(goals) != expected_count
        or any('@tapp1_fapp0 K Cat_cat E D x y FF p' not in goal for goal in goals)):
    raise SystemExit('failure is outside the recorded generic endpoint comparison')
if sys.argv[2] == 'object':
    if not all('@tapp0_fapp0 K Cat_cat E D' in goal and '@fapp0' in goal for goal in goals):
        raise SystemExit('object-cut rejection changed')
elif '@hom_postcomp_fapp0 Cat_cat Cat_cat' not in goals[0]:
    raise SystemExit('stable-head rejection changed')
print('rejected at the recorded generic endpoint comparison')
PY
}

check_target active family_section_strict_transport_empty_reproducer.lp active-later-lemma
check_target cuts family_section_object_cuts_empty_reproducer.lp cuts-object
check_target cuts family_section_profile_controls.lp cuts-controls
reject_at_endpoint without_object_cuts family_section_object_cuts_empty_reproducer.lp \
  without-object-negative object
check_target without_object_cuts family_section_stable_cuts_empty_reproducer.lp without-object-stable
check_target without_object_cuts family_section_profile_controls.lp without-object-controls
check_target without_four_endpoint_cuts family_section_profile_controls.lp without-four-controls
reject_at_endpoint without_four_endpoint_cuts family_section_object_cuts_empty_reproducer.lp \
  without-four-object-negative object
reject_at_endpoint without_four_endpoint_cuts family_section_stable_cuts_empty_reproducer.lp \
  without-four-stable-negative stable

for variant in cuts without_object_cuts without_four_endpoint_cuts; do
  python3 scripts/audit_rule_lhs.py "$stage_root/$variant/emdash3_2.lp" --strict \
    >"$stage_root/logs/$variant.lhs.txt"
done
for file in family_section_strict_transport_empty_reproducer.lp \
    family_section_object_cuts_empty_reproducer.lp \
    family_section_stable_cuts_empty_reproducer.lp family_section_profile_controls.lp; do
  python3 scripts/audit_rule_lhs.py "$source_root/audits/$file" --strict \
    >"$stage_root/logs/$file.lhs.txt"
done

python3 - "$source_root" "$stage_root" <<'PY'
from collections import Counter
from pathlib import Path
import difflib
import json
import sys
root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from warning_summary import warning_inventory
names = ['active-later-lemma', 'cuts-object', 'cuts-controls',
         'without-object-stable', 'without-object-controls', 'without-four-controls']
inv = {n: warning_inventory((stage / f'logs/{n}.log').read_text().splitlines()) for n in names}
baseline = inv['cuts-controls']
if baseline.categories != Counter({'unjoinable critical pair': 856, 'replaceable pattern variable': 134}):
    raise SystemExit('prefix warning counts changed; review the raw stream')
if inv['cuts-object'] != baseline or inv['without-object-stable'] != inv['without-object-controls']:
    raise SystemExit('rule-free consumer changes the complete source warning inventory')
for variant, log in [('without_object_cuts', 'without-object-controls'),
                     ('without_four_endpoint_cuts', 'without-four-controls')]:
    after = inv[log]
    for field in ['categories', 'term_heads', 'rule_families', 'parser_issues']:
        if getattr(after, field) != getattr(baseline, field):
            raise SystemExit(f'{variant}: {field} changed')
    old = (stage / 'cuts/emdash3_2.lp').read_text().splitlines()
    new = (stage / variant / 'emdash3_2.lp').read_text().splitlines()
    line_map = {}
    for block in difflib.SequenceMatcher(a=old, b=new, autojunk=False).get_matching_blocks():
        for offset in range(block.size):
            line_map[block.a + offset + 1] = block.b + offset + 1
    mapped = Counter()
    for location, count in baseline.locations.items():
        path, line = location.rsplit(':', 1)
        if int(line) not in line_map:
            raise SystemExit(f'{variant}: warning at a removed/changed source line')
        mapped[f'{path}:{line_map[int(line)]}'] += count
    if mapped != after.locations:
        raise SystemExit(f'{variant}: warning locations changed after unchanged-line mapping')
path = stage / 'manifest.json'
manifest = json.loads(path.read_text())
manifest.update(
    checksCompleted=True,
    laterLemmaEmptyReproduced=True,
    earlierObjectCutsEmptyReproducedBeforeSigmaHomd=True,
    stableComparisonsEmptyReproducedWithoutObjectCuts=True,
    fourCutSubtractionRejectsRecordedRoutes=True,
    constantSectionPointControlsPreserved=True,
    warningInventoriesAgreeAfterSourceLineMapping=True,
    activeWarnings=dict(inv['active-later-lemma'].categories),
    prefixWarnings=dict(baseline.categories),
    lhsAudit='all three prefix variants and four fixtures passed',
)
path.write_text(json.dumps(manifest, indent=2) + '\n')
print('source/consumer warnings agree; subtraction variants preserve the mapped warning inventory')
PY
printf 'diagnostic checks passed; this is isolation evidence, not a profile repair\n'
