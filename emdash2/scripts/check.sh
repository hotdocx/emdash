#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# During early development, a “hung” typecheck usually indicates a rewrite/unification issue.
# Default to a short timeout to avoid editor/CI lockups; override via EMDASH_TYPECHECK_TIMEOUT.
: "${EMDASH_TYPECHECK_TIMEOUT:=60s}"

check_file() {
  local file="$1"
  if command -v timeout >/dev/null 2>&1; then
    timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" lambdapi check -w "$file"
  else
    lambdapi check -w "$file"
  fi
}

check_file emdash2.lp
check_file emdash3_2.lp
