#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Catch stale active-workflow references to the retired v2 baseline. The
# retirement audit is allowed to name the old files; ignored scratchpad content
# is intentionally outside the normal scan.
RG_ARGS=(
  --line-number
  --fixed-strings
  --glob '!node_modules/**'
  --glob '!print/node_modules/**'
  --glob '!print/dist/**'
  --glob '!logs/**'
  --glob '!.scratchpad/**'
  --glob '!scripts/lint_active_refs.sh'
  --glob '!reports/REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md'
)

PATTERNS=(
  'REPORT_EMDASH2_CONSOLIDATED'
  'lambdapi check -w emdash2.lp'
  'check_file emdash2.lp'
  'Typecheck only v2'
  'Current v2 reference'
)

failed=0
for pattern in "${PATTERNS[@]}"; do
  if rg "${RG_ARGS[@]}" "$pattern" .; then
    printf 'stale active reference found: %s\n' "$pattern" >&2
    failed=1
  fi
done

if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

printf 'active reference lint passed.\n'
