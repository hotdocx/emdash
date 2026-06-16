#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ $# -ne 1 ]]; then
  printf 'usage: %s SYMBOL\n' "$0" >&2
  printf 'example: %s homd_          # expands to emdash.emdash3_2.homd_\n' "$0" >&2
  printf 'example: %s emdash.emdash3_2.homd_\n' "$0" >&2
  exit 2
fi

symbol="$1"
if [[ "$symbol" != *.* ]]; then
  symbol="emdash.emdash3_2.${symbol}"
fi

lambdapi decision-tree "$symbol"
