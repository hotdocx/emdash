#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Measured whole-pair/certificate profile. Other checks retain the 2 GiB default.
: "${EMDASH_LP_MEMORY_MIB:=6144}"
: "${EMDASH_PROBE_TIMEOUT:=180s}"
: "${OCAMLRUNPARAM:=o=20}"
export EMDASH_LP_MEMORY_MIB EMDASH_PROBE_TIMEOUT OCAMLRUNPARAM
files=(
  emdash3_2_commutative_algebra_freyd_native_snake_pairs.lp
  emdash3_2_commutative_algebra_freyd_native_snake_pair_exactness.lp
  emdash3_2_commutative_algebra_freyd_native_snake_diagram_exactness.lp
  examples/freyd_native_snake_pair_exactness.lp
)
if [[ $# -gt 1 ]]; then
  printf 'usage: %s [registered-target.lp]\n' "$0" >&2; exit 2
fi
if [[ $# -eq 1 ]]; then
  found=0
  for file in "${files[@]}"; do [[ "$file" == "$1" ]] && found=1; done
  if [[ "$found" -ne 1 ]]; then printf 'not a native snake pair target: %s\n' "$1" >&2; exit 2; fi
  files=("$1")
fi
for file in "${files[@]}"; do scripts/probe.sh "$file"; done
