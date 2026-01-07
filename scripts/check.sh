#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# During early development, a “hung” typecheck usually indicates a rewrite/unification issue.
# Default to a short timeout to avoid editor/CI lockups; override via EMDASH_TYPECHECK_TIMEOUT.
: "${EMDASH_TYPECHECK_TIMEOUT:=60s}"

# lambdapi check -w emdash.lp
if command -v timeout >/dev/null 2>&1; then
  timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" lambdapi check -w emdash2.lp
else
  lambdapi check -w emdash2.lp
fi
