#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

: "${EMDASH_TYPECHECK_TIMEOUT:=60s}"

check_file() {
  local file="$1"
  if command -v timeout >/dev/null 2>&1; then
    timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" lambdapi check -w "$file"
  else
    lambdapi check -w "$file"
  fi
}

for file in examples/*.lp; do
  printf 'checking %s\n' "$file"
  check_file "$file"
done
