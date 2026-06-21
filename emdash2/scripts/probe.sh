#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ $# -ne 1 ]]; then
  printf 'usage: %s path/to/probe.lp\n' "$0" >&2
  exit 2
fi

probe_file="$1"
if [[ ! -f "$probe_file" ]]; then
  printf 'probe file not found: %s\n' "$probe_file" >&2
  exit 2
fi

: "${EMDASH_PROBE_TIMEOUT:=${EMDASH_TYPECHECK_TIMEOUT:-30s}}"
: "${EMDASH_LAMBDAPI_WARNINGS:=0}"

warning_flags=(-w)
case "$EMDASH_LAMBDAPI_WARNINGS" in
  1|true|TRUE|yes|YES|on|ON)
    warning_flags=()
    ;;
  0|false|FALSE|no|NO|off|OFF)
    ;;
  *)
    printf 'invalid EMDASH_LAMBDAPI_WARNINGS value: %s\n' "$EMDASH_LAMBDAPI_WARNINGS" >&2
    exit 2
    ;;
esac

extra_flags=()
if [[ -n "${EMDASH_LAMBDAPI_FLAGS:-}" ]]; then
  read -r -a extra_flags <<< "$EMDASH_LAMBDAPI_FLAGS"
fi

mkdir -p logs/probes
base="$(basename "$probe_file" .lp)"
stamp="$(date +%Y%m%d-%H%M%S)"
log_file="logs/probes/${base}-${stamp}.log"

printf 'checking %s with timeout %s (warnings=%s)\n' \
  "$probe_file" "$EMDASH_PROBE_TIMEOUT" "$EMDASH_LAMBDAPI_WARNINGS"
set +e
if command -v timeout >/dev/null 2>&1; then
  timeout --signal=INT "$EMDASH_PROBE_TIMEOUT" \
    lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$probe_file" >"$log_file" 2>&1
else
  lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$probe_file" >"$log_file" 2>&1
fi
rc=$?
set -e

if [[ "$rc" -eq 0 ]]; then
  printf 'probe succeeded; log: %s\n' "$log_file"
else
  printf 'probe failed with exit %s; log: %s\n' "$rc" "$log_file" >&2
  python3 scripts/explain_failure.py "$log_file" || true
fi

exit "$rc"
