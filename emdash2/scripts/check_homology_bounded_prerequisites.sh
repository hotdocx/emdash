#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Keep each source and reviewer independently bounded while sharing only this
# fresh exact-source dependency tree. No persistent object cache or opaque proof.
: "${EMDASH_TYPECHECK_TIMEOUT:=90s}"
: "${EMDASH_LAMBDAPI_WARNINGS:=0}"
warning_flags=(-w)
case "$EMDASH_LAMBDAPI_WARNINGS" in
  1|true|TRUE|yes|YES|on|ON) warning_flags=(); mode=warnings ;;
  0|false|FALSE|no|NO|off|OFF) mode=quiet ;;
  *) printf 'invalid warning setting: %s\n' "$EMDASH_LAMBDAPI_WARNINGS" >&2; exit 2 ;;
esac
extra_flags=()
if [[ -n "${EMDASH_LAMBDAPI_FLAGS:-}" ]]; then
  read -r -a extra_flags <<< "$EMDASH_LAMBDAPI_FLAGS"
fi

prerequisites=(
  emdash3_2_homology_window.lp
  emdash3_2_homology_map_kernel_covers.lp
  emdash3_2_homology_first_exactness.lp
  emdash3_2_homology_epic_covers.lp
  emdash3_2_homology_second_exactness.lp
  emdash3_2_homology_third_exactness.lp
)
owners=(
  emdash3_2_homology_exact_window.lp
  emdash3_2_homology_exact_window_result.lp
  emdash3_2_finite_arrow_tails.lp
  emdash3_2_finite_arrow_tail_append.lp
  emdash3_2_computational_exact_arrow_tails.lp
  emdash3_2_preadditive_zero_identity.lp
  emdash3_2_homology_record_zero.lp
  emdash3_2_homology_whole_zero.lp
  emdash3_2_homology_window_extension.lp
  emdash3_2_homology_row_triples.lp
  emdash3_2_homology_row_spans.lp
)
reviewers=(
  examples/homology_adjacent_window_tails.lp
  examples/preadditive_zero_identity.lp
  examples/homology_whole_zero.lp
  examples/homology_window_extension.lp
  examples/homology_row_spans.lp
)
mkdir -p logs/probes
log_file="$(pwd)/logs/probes/homology-bounded-prerequisites-${mode}-$(date +%Y%m%d-%H%M%S).log"
stage_root="$(mktemp -d /tmp/emdash-homology-bounded-prerequisites.XXXXXX)"
cleanup() {
  case "$stage_root" in
    /tmp/emdash-homology-bounded-prerequisites.??????) ;;
    *) printf 'unexpected temporary path: %s\n' "$stage_root" >&2; return 1 ;;
  esac
  local file
  for file in "$stage_root"/*.lp "$stage_root"/*.lpo \
      "$stage_root"/*.lpi "$stage_root"/*.lpj "$stage_root"/lambdapi.pkg \
      "$stage_root"/examples/*.lp "$stage_root"/examples/*.lpo \
      "$stage_root"/examples/*.lpi "$stage_root"/examples/*.lpj; do
    if [[ -f "$file" || -L "$file" ]]; then unlink -- "$file"; fi
  done
  rmdir -- "$stage_root/examples" "$stage_root"
}
trap cleanup EXIT
mkdir -p "$stage_root/examples"
cp lambdapi.pkg ./*.lp "$stage_root/"
for file in "${reviewers[@]}"; do cp "$file" "$stage_root/examples/"; done

check_object() {
  local file="$1" started="$SECONDS" rc elapsed
  printf 'checking %s with fresh exact objects (timeout %s, %s)\n' \
    "$file" "$EMDASH_TYPECHECK_TIMEOUT" "$mode"
  printf 'checking %s with fresh exact objects (timeout %s, %s)\n' \
    "$file" "$EMDASH_TYPECHECK_TIMEOUT" "$mode" >>"$log_file"
  set +e
  timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" \
    lambdapi check -c --no-colors "${warning_flags[@]}" "${extra_flags[@]}" \
    "$file" >>"$log_file" 2>&1
  rc=$?
  set -e
  elapsed=$((SECONDS - started))
  printf 'finished %s: exit %s, elapsed %ss\n' "$file" "$rc" "$elapsed"
  printf 'finished %s: exit %s, elapsed %ss\n' "$file" "$rc" "$elapsed" >>"$log_file"
  if [[ "$rc" -ne 0 ]]; then
    tail -30 "$log_file" | cut -c1-260 >&2
    printf 'check failed; log: %s\n' "$log_file" >&2
    return "$rc"
  fi
}

printf 'homology-bounded-prerequisites check log: %s\n' "$log_file"
cd "$stage_root"
check_object emdash3_2.lp
for file in "${prerequisites[@]}" "${owners[@]}"; do check_object "$file"; done
for file in "${reviewers[@]}"; do check_object "$file"; done
printf 'homology-bounded-prerequisites checks succeeded; log: %s\n' "$log_file"
