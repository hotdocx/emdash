#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Measured profile for this complete native result. It changes collection
# frequency only; all checks still use the normal serial resource guard.
: "${OCAMLRUNPARAM:=o=20}"
export OCAMLRUNPARAM

files=(
  emdash3_2_one_cat_native_exact_arrow_pairs.lp
  emdash3_2_one_cat_native_exact_tail_observations.lp
  emdash3_2_one_cat_native_snake_six_term_result.lp
  examples/one_cat_native_exact_arrow_pairs.lp
  examples/one_cat_native_exact_tail_observations.lp
  examples/one_cat_native_snake_six_term_result.lp
  examples/one_cat_native_snake_six_term_inputs.lp
  examples/one_cat_native_snake_six_term_data.lp
)
if [[ $# -gt 1 ]]; then
  printf 'usage: %s [registered-target.lp]\n' "$0" >&2
  exit 2
fi
if [[ $# -eq 1 ]]; then
  selected=0
  for file in "${files[@]}"; do
    if [[ "$file" == "$1" ]]; then selected=1; break; fi
  done
  if [[ "$selected" -ne 1 ]]; then
    printf 'not a native six-term check target: %s\n' "$1" >&2
    exit 2
  fi
  files=("$1")
fi

printf 'native six-term GC profile: %s\n' "$OCAMLRUNPARAM"
for file in "${files[@]}"; do
  scripts/probe.sh "$file"
done
