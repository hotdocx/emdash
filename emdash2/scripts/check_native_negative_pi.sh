#!/usr/bin/env bash
# NON-LIBRARY native negative-section prototype over the preferred Op prefix.
# A passing prefix/prototype is not a full-kernel or Homd-target qualification.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"

[[ "$(git hash-object emdash3_2.lp)" == 91f1974ece225e399604dce24710bf1437ad3ef5 ]] || {
  printf 'native core anchor changed; review this prefix experiment first\n' >&2
  exit 2
}
[[ "$(git hash-object audits/total_op_reinterpretation.patch)" == 4d4c8a753bd0bfdada8a8e01eca2774d9c17c4c2 ]] || {
  printf 'preferred-duality patch changed; review this experiment first\n' >&2
  exit 2
}

stage_root="$(mktemp -d /tmp/emdash-native-negative-pi.XXXXXX)"
python3 - "$source_root" "$stage_root" <<'PY'
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

root, stage = map(Path, sys.argv[1:])
historical = stage / 'historical'
historical.mkdir()
old_blob = '5387c65ab75ddcfff4b5ffca9fb6f9d082084774'
old = subprocess.check_output(['git', 'cat-file', 'blob', old_blob], cwd=root)
marker = '// 12. Directed homd target and internal homd functor'
for dest, content in [(stage, (root / 'emdash3_2.lp').read_bytes()), (historical, old)]:
    (dest / 'emdash3_2.lp').write_bytes(content)
    shutil.copyfile(root / 'lambdapi.pkg', dest / 'lambdapi.pkg')
    with (dest / 'patch.log').open('w') as log:
        subprocess.run(['patch', '--batch', '--forward', '--fuzz=0', '-p1', '-i',
                        str(root / 'audits/total_op_reinterpretation.patch')],
                       cwd=dest, stdout=log, stderr=subprocess.STDOUT, check=True)
    full = (dest / 'emdash3_2.lp').read_text()
    if full.count(marker) != 1:
        raise SystemExit('native Homd boundary marker is not unique')
    (dest / 'full_kernel_candidate.lp').write_text(full)
    (dest / 'emdash3_2.lp').write_text(full.split(marker)[0])
if (stage / 'emdash3_2.lp').read_bytes() != (historical / 'emdash3_2.lp').read_bytes():
    raise SystemExit('current and historical preferred prefixes differ; review required')
shutil.copyfile(root / 'audits/native_negative_pi_prototype.lp',
                stage / 'native_negative_pi_prototype.lp')
(stage / 'logs').mkdir()
names = ['emdash3_2.lp', 'native_negative_pi_prototype.lp', 'full_kernel_candidate.lp']
manifest = {
    'scope': 'preferred-prefix and negative-section prototype only',
    'fullKernelChecked': False,
    'currentSourceBlob': '91f1974ece225e399604dce24710bf1437ad3ef5',
    'historicalSourceBlob': old_blob,
    'matchingHistoricalPrefix': True,
    'sha256': {name: hashlib.sha256((stage / name).read_bytes()).hexdigest()
               for name in names},
}
(stage / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
PY

printf 'non-library prefix only; full native Homd target remains unqualified\n'
printf 'retained source and logs: %s\n' "$stage_root"

check_target() {
  local file="$1"
  local log="$stage_root/logs/$file.log"
  printf 'checking %s with the repository resource guard\n' "$file"
  if ! (cd "$stage_root" && bash "$source_root/scripts/lambdapi_resource_guard.sh" \
      lambdapi check --no-colors "$file") >"$log" 2>&1; then
    python3 "$source_root/scripts/explain_failure.py" "$log" || true
    printf 'candidate failed; inspect %s\n' "$log" >&2
    return 1
  fi
}

# Separate guarded invocations; imports and sources are local to this stage.
check_target emdash3_2.lp
check_target native_negative_pi_prototype.lp
for name in emdash3_2.lp native_negative_pi_prototype.lp; do
  python3 scripts/warning_summary.py "$stage_root/logs/$name.log" --strict-parse \
    > "$stage_root/logs/$name.warnings.txt"
done
python3 - "$source_root" "$stage_root" <<'PY'
from pathlib import Path
import sys
root, stage = map(Path, sys.argv[1:])
sys.path.insert(0, str(root / 'scripts'))
from warning_summary import warning_inventory
logs = [stage / 'logs' / f'{name}.log'
        for name in ['emdash3_2.lp', 'native_negative_pi_prototype.lp']]
inventories = [warning_inventory(path.read_text().splitlines()) for path in logs]
if inventories[0] != inventories[1]:
    raise SystemExit('prototype warning inventory differs from its exact prefix')
print('complete warning inventories agree')
PY
python3 scripts/audit_rule_lhs.py audits/native_negative_pi_prototype.lp --strict \
  > "$stage_root/logs/negative-pi-lhs.txt"
printf 'negative-section prototype checks passed; active kernel unchanged\n'
