#!/usr/bin/env bash
set -euo pipefail

# Check the retained nonsplit workflow and its emitted native observer in
# separate bounded processes. Compile only the affected test dependency tree.
# --bounded checks the complete retained inventory, reuse and all three windows.
bounded=0
if [[ $# -eq 1 && "$1" == --bounded ]]; then
  bounded=1
elif [[ $# -ne 0 ]]; then
  printf 'usage: %s [--bounded]\n' "$0" >&2
  exit 2
fi
kernel_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
repo_root="$(cd -- "$kernel_root/.." && pwd)"
cd "$repo_root"
mkdir -p "$kernel_root/tmp/probes" "$kernel_root/logs/probes"
stage_root="$(mktemp -d "$kernel_root/tmp/native_connecting_XXXXXX")"
stamp="$(date +%Y%m%d_%H%M%S)_$$"
log_file="$kernel_root/logs/probes/native_connecting_${stamp}.log"
artifact="$kernel_root/tmp/probes/native_connecting_${stamp}.lp"
test_file="tests/v3_2_algebra_formal_freyd_actual_homology_tests.ts"
if (( bounded )); then
  artifact="$kernel_root/tmp/probes/native_connecting_${stamp}"
  test_file="tests/v3_2_algebra_formal_freyd_long_exact_homology_tests.ts"
fi
guard="$kernel_root/scripts/lambdapi_resource_guard.sh"

cleanup() {
  # This fresh directory contains only this command's generated compiler output.
  python3 - "$stage_root" "$kernel_root/tmp" <<'PY'
from pathlib import Path
import shutil, sys
stage, parent = map(Path, sys.argv[1:])
if stage.parent != parent or not stage.name.startswith('native_connecting_'):
    raise SystemExit('Unexpected native connecting stage path')
shutil.rmtree(stage)
PY
}
trap cleanup EXIT

python3 - "$stage_root" "$repo_root" "$test_file" <<'PY'
from pathlib import Path
import json, sys
stage, root, test_file = map(Path, sys.argv[1:])
out = stage / 'compiled'
out.mkdir()
(out / 'package.json').write_text('{"private":true,"type":"commonjs"}\n')
(stage / 'tsconfig.json').write_text(json.dumps({
    'extends': str(root / 'tsconfig.json'),
    'compilerOptions': {
        'rootDir': str(root), 'outDir': str(out), 'noEmit': False,
        'noEmitOnError': True, 'sourceMap': False, 'declaration': False,
        'incremental': False
    },
    'files': [str(root / test_file)],
    'include': [], 'exclude': []
}, indent=2) + '\n')
(stage / 'worker-limits.cjs').write_text("""
require('node:test').test('bounded worker V8 heap limit', () => {
  const limit = require('node:v8').getHeapStatistics().heap_size_limit;
  require('node:assert/strict').ok(limit <= 544 * 1024 * 1024,
    'V8 worker did not inherit the selected heap limit: ' + limit);
  process.stdout.write('worker V8 heap limit: ' + limit + ' bytes\\n');
});
""")
PY

run_step() {
  local label="$1" rc
  shift
  printf 'checking %s\n' "$label"
  printf 'checking %s\n' "$label" >>"$log_file"
  if "$@" >>"$log_file" 2>&1; then
    printf 'passed %s\n' "$label"
  else
    rc=$?
    tail -35 "$log_file" | cut -c1-280 >&2
    printf 'failed %s; log: %s\n' "$label" "$log_file" >&2
    return "$rc"
  fi
}

run_step focused-types "$guard" node --max-old-space-size=768 \
  "$repo_root/node_modules/typescript/bin/tsc" -p "$stage_root/tsconfig.json"
if (( bounded )); then
  # This Node build drops CLI V8 flags when spawning isolated test workers.
  # NODE_OPTIONS is inherited; verify the worker before the expensive fixture.
  worker_options="${NODE_OPTIONS:+$NODE_OPTIONS }--max-old-space-size=512 --max-semi-space-size=4"
  run_step worker-heap-limit env NODE_OPTIONS="$worker_options" \
    "$guard" node --test "$stage_root/worker-limits.cjs"
  run_step full-inventory-and-emission env EMDASH_LP_TIMEOUT=300s \
    NODE_OPTIONS="$worker_options" \
    EMDASH_PROOF_CAS_BOUNDED_CONNECTING_PROBE_DIR="$artifact" \
    "$guard" node --max-old-space-size=512 --max-semi-space-size=4 --test \
    --test-name-pattern='observes every retained H point|rejects invalid bounded model|upgrades the adopted prefix|reuses all connecting claims|checks the complete bounded connecting inventory' \
    "$stage_root/compiled/tests/v3_2_algebra_formal_freyd_long_exact_homology_tests.js"
  python3 - "$artifact" <<'PY'
from pathlib import Path
import json, sys
root = Path(sys.argv[1])
manifest = json.loads((root / 'manifest.json').read_text())
assert [(x['degree'], x['position']) for x in manifest['windows']] == [(0, 6), (1, 3), (2, 0)]
assert manifest['counts']['points'] == 18 and manifest['counts']['maps'] == 8
assert manifest['counts']['connectings'] == 3
assert all((root / x['file']).is_file() and x['assertions'] == 6 for x in manifest['windows'])
PY
  for degree in 0 1 2; do
    run_step "emitted-native-window-$degree" "$kernel_root/scripts/probe.sh" \
      "$artifact/connecting_$degree.lp"
  done
else
  run_step adoption-and-emission env \
    NODE_OPTIONS="${NODE_OPTIONS:+$NODE_OPTIONS }--max-old-space-size=512" \
    EMDASH_RUN_PROOF_CAS_FREYD_MODEL_CONNECTING_ADOPTION=1 \
    EMDASH_PROOF_CAS_NATIVE_CONNECTING_PROBE_OUTPUT="$artifact" \
    "$guard" node --max-old-space-size=512 --test \
    --test-name-pattern='adopts a retained nonsplit connecting arrow|constructs the exact conditional|rejects legacy normality|rejects missing normality' \
    "$stage_root/compiled/tests/v3_2_algebra_formal_freyd_actual_homology_tests.js"
  test -s "$artifact"
  run_step emitted-native-observer "$kernel_root/scripts/probe.sh" "$artifact"
fi
printf 'native model connecting passed; probe: %s; log: %s\n' "$artifact" "$log_file"
