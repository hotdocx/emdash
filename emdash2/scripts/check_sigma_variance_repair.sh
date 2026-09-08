#!/usr/bin/env bash
# NON-LIBRARY experiment: stage the exact owner-position Sigma patch.
# This does not edit the active nucleus, qualify internal op, or run aggregates.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"

# Full-file anchors protect the zero-context patch from source drift. Zero
# context keeps patch-only blank markers out of the repository whitespace lint.
anchors=(
  'emdash3_2.lp:5387c65ab75ddcfff4b5ffca9fb6f9d082084774'
  'emdash3_2_dependent_simplex_bridge.lp:ac53ce23384811c32ecf0b9a7b76e597d85c0794'
  'examples/dependent_hom_laxity.lp:99fc6ceaae691447e70c6457b2c96cba078cacf6'
  'examples/dependent_simplex_bridge.lp:bebf0f5f3838d4416fb25c2021d35e804128d673'
  'examples/dependent_simplex_profiles.lp:703419d51046085c7da6dd86c3eb6c7370f31a9a'
  'examples/dependent_simplex_represented_source.lp:c8067b2cdf45bed0ee1fd5a78fe3e5d1e9568ca7'
)
for anchor in "${anchors[@]}"; do
  file="${anchor%%:*}"
  expected="${anchor#*:}"
  actual="$(git hash-object "$file")"
  if [[ "$actual" != "$expected" ]]; then
    printf 'candidate anchor changed: %s; review/rebase the audit patch explicitly\n' "$file" >&2
    exit 2
  fi
done

reviewers=(
  examples/sigma_total.lp
  examples/fibrewise_sigma.lp
  examples/dependent_simplex_bridge.lp
  examples/dependent_simplex_profiles.lp
  examples/dependent_simplex_represented_source.lp
  examples/dependent_simplex_native_dimensions.lp
  examples/chain_pair_native_triangles.lp
  examples/pathout_transformation_lift.lp
  examples/dependent_hom_laxity.lp
  examples/cubical_arrow.lp
  examples/cubical_arrow_functor.lp
  examples/chain_pair_cubical_maps.lp
  examples/pullbacks.lp
  audits/sigma_hom_variance_repair_checks.lp
)
stage_root="$(mktemp -d /tmp/emdash-sigma-variance-audit.XXXXXX)"
printf 'isolated candidate package and logs: %s\n' "$stage_root"
mkdir -p "$stage_root/examples" "$stage_root/audits" "$stage_root/logs"
cp lambdapi.pkg ./*.lp "$stage_root/"
for file in "${reviewers[@]}" \
    audits/sigma_hom_empty_reproducer.lp audits/internal_op_empty_reproducer.lp; do
  cp "$file" "$stage_root/$file"
done
patch --batch --forward --fuzz=0 --directory "$stage_root" -p1 \
  < audits/sigma_hom_variance_repair.patch > "$stage_root/logs/patch.log"

check_target() {
  local file="$1"
  shift
  local log="$stage_root/logs/${file//\//_}.log"
  printf 'checking %s (90 seconds maximum)\n' "$file"
  if ! timeout --signal=INT 90s lambdapi check -c --no-colors "$@" "$file" > "$log" 2>&1; then
    printf 'unexpected failure; inspect %s\n' "$log" >&2
    return 1
  fi
}

cd "$stage_root"
check_target emdash3_2.lp
python3 "$source_root/scripts/warning_summary.py" \
  "$stage_root/logs/emdash3_2.lp.log" --strict-parse \
  > "$stage_root/logs/core-warning-summary.txt"
python3 "$source_root/scripts/audit_rule_lhs.py" "$stage_root/emdash3_2.lp" --strict \
  > "$stage_root/logs/core-lhs-audit.txt"
for file in "${reviewers[@]}"; do check_target "$file" -w; done

# The original Sigma derivation must fail at the invalid generic Hom cast,
# not because a symbol/import is missing, the process times out, or it crashes.
negative_log="$stage_root/logs/sigma-original-expected-rejection.log"
set +e
timeout --signal=INT 90s lambdapi check -w --no-colors \
  audits/sigma_hom_empty_reproducer.lp > "$negative_log" 2>&1
negative_rc=$?
set -e
if [[ "$negative_rc" -ne 1 ]] || \
    ! rg -q 'The proof is not finished:' "$negative_log" || \
    ! rg -q 'Sigma_cat.*All_catd.*≡ CoAll_cat.*Sigma_cat' "$negative_log"; then
  printf 'unexpected Sigma negative result (%s); inspect %s\n' "$negative_rc" "$negative_log" >&2
  exit 1
fi
printf 'original Sigma derivation rejected at its typed Hom cast\n'

# Fault-isolation control, NOT a positive library test or consistency claim.
check_target audits/internal_op_empty_reproducer.lp -w
printf 'known independent internal-op derivation remains accepted; op is NOT repaired\n'
printf 'scoped Sigma experiment passed; active source unchanged; evidence retained in %s\n' "$stage_root"
