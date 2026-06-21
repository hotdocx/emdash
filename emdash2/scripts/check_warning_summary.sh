#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

: "${EMDASH_WARNING_TIMEOUT:=${EMDASH_TYPECHECK_TIMEOUT:-60s}}"
: "${EMDASH_WARNING_LOG:=logs/warnings/latest.log}"

mkdir -p "$(dirname "$EMDASH_WARNING_LOG")"

printf 'checking emdash3_2.lp with warnings enabled (timeout %s)\n' \
  "$EMDASH_WARNING_TIMEOUT"

set +e
if command -v timeout >/dev/null 2>&1; then
  timeout --signal=INT "$EMDASH_WARNING_TIMEOUT" \
    lambdapi check --no-colors emdash3_2.lp >"$EMDASH_WARNING_LOG" 2>&1
else
  lambdapi check --no-colors emdash3_2.lp >"$EMDASH_WARNING_LOG" 2>&1
fi
rc=$?
set -e

python3 scripts/warning_summary.py "$EMDASH_WARNING_LOG"
printf '\nraw warning log: %s\n' "$EMDASH_WARNING_LOG"
exit "$rc"
