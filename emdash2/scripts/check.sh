#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# During early development, a “hung” typecheck usually indicates a rewrite/unification issue.
# Default to a short timeout to avoid editor/CI lockups; override via EMDASH_TYPECHECK_TIMEOUT.
: "${EMDASH_TYPECHECK_TIMEOUT:=60s}"
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

check_file() {
  local file="$1"
  if command -v timeout >/dev/null 2>&1; then
    timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" \
      lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  else
    lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  fi
}

files=("$@")
if [[ ${#files[@]} -eq 0 ]]; then
  files=(emdash3_2.lp emdash3_2_checks.lp)
fi

for file in "${files[@]}"; do
  check_file "$file"
done
