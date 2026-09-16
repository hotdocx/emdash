#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
formal_root="$(pwd)"

: "${EMDASH_TYPECHECK_TIMEOUT:=90s}"
: "${EMDASH_LAMBDAPI_WARNINGS:=0}"
warning_flags=(-w)
case "$EMDASH_LAMBDAPI_WARNINGS" in
  1|true|TRUE|yes|YES|on|ON) warning_flags=() ;;
  0|false|FALSE|no|NO|off|OFF) ;;
  *) printf 'invalid warning setting: %s\n' "$EMDASH_LAMBDAPI_WARNINGS" >&2; exit 2 ;;
esac
extra_flags=()
if [[ -n "${EMDASH_LAMBDAPI_FLAGS:-}" ]]; then
  read -r -a extra_flags <<< "$EMDASH_LAMBDAPI_FLAGS"
fi

owners=(
  emdash3_2_kernel_domain_comparison.lp
  emdash3_2_cokernel_codomain_comparison.lp
  emdash3_2_abelian_structure_elimination.lp
)
reviewers=(
  examples/abelian_structure_elimination.lp
)
stage_root="$(mktemp -d /tmp/emdash-ordinary-rows.XXXXXX)"
mkdir -p "$stage_root/examples"
cleanup() {
  case "$stage_root" in
    /tmp/emdash-ordinary-rows.??????) ;;
    *) printf 'unexpected temporary path: %s\n' "$stage_root" >&2; return 1 ;;
  esac
  # Only generated/copied file kinds are removed; unexpected content survives.
  local file
  for file in "$stage_root"/*.lp "$stage_root"/*.lpo \
      "$stage_root"/*.lpi "$stage_root"/*.lpj \
      "$stage_root"/lambdapi.pkg "$stage_root"/examples/*.lp \
      "$stage_root"/examples/*.lpo; do
    if [[ -f "$file" || -L "$file" ]]; then unlink -- "$file"; fi
  done
  rmdir -- "$stage_root/examples" "$stage_root"
}
trap cleanup EXIT
cp lambdapi.pkg ./*.lp "$stage_root/"
for file in "${reviewers[@]}"; do cp "$file" "$stage_root/examples/"; done

check_object() {
  printf 'checking %s with fresh exact dependency objects\n' "$1"
  EMDASH_LP_TIMEOUT="$EMDASH_TYPECHECK_TIMEOUT" \
    bash "$formal_root/scripts/lambdapi_resource_guard.sh" lambdapi check -c "${warning_flags[@]}" "${extra_flags[@]}" "$1"
}
cd "$stage_root"
# Recheck exact source dependencies, then retain only these temporary objects
# across the independently bounded consumer checks. No proof is made opaque.
check_object emdash3_2.lp
for file in "${owners[@]}" "${reviewers[@]}"; do check_object "$file"; done
