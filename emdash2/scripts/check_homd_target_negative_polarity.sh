#!/usr/bin/env bash
# NON-LIBRARY full-source polarity isolation. Old op/Sigma defects remain.
# This does not qualify the preferred total-duality repair or library migration.
# The patch has zero context; its exact source anchor is checked below.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"

[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'native core anchor changed; review this isolation first\n' >&2
  exit 2
}

stage_root="$(mktemp -d /tmp/emdash-homd-negative-polarity.XXXXXX)"
python3 - "$source_root" "$stage_root" <<'PY'
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

root, stage = map(Path, sys.argv[1:])
for name in ['baseline', 'candidate']:
    dest = stage / name
    dest.mkdir()
    for file in ['emdash3_2.lp', 'lambdapi.pkg']:
        shutil.copyfile(root / file, dest / file)
(stage / 'logs').mkdir()
candidate = stage / 'candidate'
with (stage / 'logs/patch.log').open('w') as log:
    subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
                    str(root / 'audits/homd_target_negative_polarity.patch')],
                   cwd=candidate, stdout=log, stderr=subprocess.STDOUT, check=True)
files = ['homd_target_negative_polarity_controls.lp',
         'homd_target_constant_comparison_controls.lp',
         'homd_target_empty_reproducer.lp']
for file in files:
    shutil.copyfile(root / 'audits' / file, candidate / file)
manifest = {
    'scope': 'full-source section-polarity isolation; old op/Sigma defects retained',
    'preferredDualityRepair': False,
    'libraryConsumerMigration': False,
    'activeKernelModified': False,
    'checksCompleted': False,
    'sourceBlob': '91f1974ece225e399604dce24710bf1437ad3ef5',
    'sha256': {
        str(path.relative_to(stage)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [stage / 'baseline/emdash3_2.lp', candidate / 'emdash3_2.lp',
                     *[candidate / file for file in files]]
    },
}
(stage / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY

printf 'polarity isolation only; old op/Sigma defects are retained\n'
printf 'retained sources and logs: %s\n' "$stage_root"

check_target() {
  local variant="$1" file="$2" label="$3"
  local log="$stage_root/logs/$label.log"
  printf 'checking %s/%s with the repository resource guard\n' "$variant" "$file"
  if ! (cd "$stage_root/$variant" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
      lambdapi check --no-colors "$file") >"$log" 2>&1; then
    python3 "$source_root/scripts/explain_failure.py" "$log" || true
    printf 'isolation check failed; inspect %s\n' "$log" >&2
    return 1
  fi
}

# Each full source/consumer has its own guarded, serial checker invocation.
check_target baseline emdash3_2.lp baseline
check_target candidate emdash3_2.lp candidate
check_target candidate homd_target_negative_polarity_controls.lp native-controls
check_target candidate homd_target_constant_comparison_controls.lp constant-controls

# The historical Empty route must fail for the positive/negative family
# mismatch, not a missing symbol/import, syntax error or resource exhaustion.
negative_status=0
(cd "$stage_root/candidate" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
    lambdapi check -w --no-colors homd_target_empty_reproducer.lp) \
    >"$stage_root/logs/old-empty-negative.log" 2>&1 || negative_status=$?
[[ "$negative_status" == 1 ]] || {
  printf 'old target fixture returned %s; expected a type failure (1)\n' "$negative_status" >&2
  exit 1
}
python3 - "$stage_root/logs/old-empty-negative.log" <<'PY'
from pathlib import Path
import sys
text = Path(sys.argv[1]).read_text()
goals = [line for line in text.splitlines() if line.startswith('0. ')]
if ('The proof is not finished:' not in text or len(goals) != 1
        or '@Functor_catd (Op_cat Z)' not in goals[0]
        or ' ≡ @Op_catd (Op_cat Z)' not in goals[0]):
    raise SystemExit('negative fixture failed outside the recorded section-polarity goal')
print('old Empty route rejected at its recorded positive/negative family mismatch')
PY

for file in emdash3_2.lp homd_target_negative_polarity_controls.lp \
    homd_target_constant_comparison_controls.lp; do
  python3 scripts/audit_rule_lhs.py "$stage_root/candidate/$file" --strict \
    >"$stage_root/logs/$file.lhs.txt"
done

python3 - "$source_root" "$stage_root" <<'PY'
from pathlib import Path
from collections import Counter
import difflib
import json
import sys

root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from warning_summary import warning_inventory

names = ['baseline', 'candidate', 'native-controls', 'constant-controls']
inventories = {name: warning_inventory((stage / f'logs/{name}.log').read_text().splitlines())
               for name in names}
before, after = inventories['baseline'], inventories['candidate']
for field in ['categories', 'term_heads', 'rule_families', 'parser_issues']:
    if getattr(before, field) != getattr(after, field):
        raise SystemExit(f'changed {field}; review warnings before accepting this experiment')
old = (stage / 'baseline/emdash3_2.lp').read_text().splitlines()
new = (stage / 'candidate/emdash3_2.lp').read_text().splitlines()
line_map = {}
for block in difflib.SequenceMatcher(a=old, b=new, autojunk=False).get_matching_blocks():
    for offset in range(block.size):
        line_map[block.a + offset + 1] = block.b + offset + 1
locations = Counter()
for location, count in before.locations.items():
    path, line = location.rsplit(':', 1)
    mapped = line_map.get(int(line))
    if mapped is None:
        raise SystemExit(f'warning at changed source line {location}; review required')
    locations[f'{path}:{mapped}'] += count
if locations != after.locations:
    raise SystemExit('warning locations differ after exact unchanged-line mapping')
for name in ['native-controls', 'constant-controls']:
    if inventories[name] != after:
        raise SystemExit(f'{name} changes the complete candidate warning inventory')
manifest_path = stage / 'manifest.json'
manifest = json.loads(manifest_path.read_text())
manifest.update(checksCompleted=True,
                oldEmptyRejectedAt='positive versus negative section family',
                warnings=dict(after.categories),
                warningInventoriesAgreeAfterSourceLineMapping=True,
                lhsAudit='full copied core and both reviewers passed')
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
print('warning inventories agree after source-line mapping; reviewer inventories agree exactly')
PY
printf 'polarity isolation checks passed; active kernel unchanged and full repair still pending\n'
