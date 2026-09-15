#!/usr/bin/env bash
set -euo pipefail

# Check the retained nonsplit workflow and its emitted native observer in
# separate bounded processes. Compile only the affected test dependency tree.
kernel_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
repo_root="$(cd -- "$kernel_root/.." && pwd)"
cd "$repo_root"
mkdir -p "$kernel_root/tmp/probes" "$kernel_root/logs/probes"
stage_root="$(mktemp -d "$kernel_root/tmp/native_connecting_XXXXXX")"
stamp="$(date +%Y%m%d_%H%M%S)_$$"
log_file="$kernel_root/logs/probes/native_connecting_${stamp}.log"
artifact="$kernel_root/tmp/probes/native_connecting_${stamp}.lp"
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

python3 - "$stage_root" "$repo_root" <<'PY'
from pathlib import Path
import json, sys
stage, root = map(Path, sys.argv[1:])
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
    'files': [str(root / 'tests/v3_2_algebra_formal_freyd_actual_homology_tests.ts')],
    'include': [], 'exclude': []
}, indent=2) + '\n')
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
run_step adoption-and-emission env \
  EMDASH_RUN_PROOF_CAS_FREYD_MODEL_CONNECTING_ADOPTION=1 \
  EMDASH_PROOF_CAS_NATIVE_CONNECTING_PROBE_OUTPUT="$artifact" \
  "$guard" node --max-old-space-size=512 --test \
  --test-name-pattern='adopts a retained nonsplit connecting arrow|constructs the exact conditional|rejects legacy normality|rejects missing normality' \
  "$stage_root/compiled/tests/v3_2_algebra_formal_freyd_actual_homology_tests.js"
test -s "$artifact"
run_step emitted-native-observer "$kernel_root/scripts/probe.sh" "$artifact"
printf 'native model connecting passed; probe: %s; log: %s\n' "$artifact" "$log_file"
