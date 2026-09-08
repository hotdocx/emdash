#!/usr/bin/env bash
# Non-library qualification of the preferred total-Op/CoAbove2 source prefix.
# The old Homd target and later declarations remain outside this partial gate.
set -euo pipefail
cd "$(dirname "$0")/.."
source_root="$PWD"
if [[ "$(git hash-object emdash3_2.lp)" != 5387c65ab75ddcfff4b5ffca9fb6f9d082084774 ]]; then
  printf 'core anchor changed; review the total-op audit patch explicitly\n' >&2
  exit 2
fi
stage_root="$(mktemp -d /tmp/emdash-total-op-prefix.XXXXXX)"
printf 'prefix-only audit; full Homd migration is NOT qualified\n'
printf 'retained source copies and logs: %s\n' "$stage_root"
mkdir -p "$stage_root/audits" "$stage_root/logs"
cp lambdapi.pkg emdash3_2.lp "$stage_root/"
# Generated exact prefixes are test inputs, not edits to the active source.
sed '/^\/\/ 12\. Directed homd target and internal homd functor/,$d' \
  emdash3_2.lp > "$stage_root/baseline_prefix.lp"
patch --batch --forward --fuzz=0 --directory "$stage_root" -p1 \
  < audits/total_op_reinterpretation.patch > "$stage_root/logs/patch.log"
mv "$stage_root/emdash3_2.lp" "$stage_root/full_kernel_candidate.lp"
sed '/^\/\/ 12\. Directed homd target and internal homd functor/,$d' \
  "$stage_root/full_kernel_candidate.lp" > "$stage_root/emdash3_2.lp"
cp audits/total_op_basis_checks.lp audits/total_op_sigma_checks.lp \
  audits/internal_op_empty_reproducer.lp audits/internal_op_family_empty_reproducer.lp \
  "$stage_root/audits/"
# Keep the old Sigma diagnostic's dimension-1 meaning after the reinterpretation.
# Both its endpoints remain well-formed; the invalid conversion must be rejected.
sed -e 's/\<Op_cat\>/Transpose_cat/g' -e 's/\<Op_func\>/Transpose_func/g' \
  audits/sigma_hom_empty_reproducer.lp > "$stage_root/audits/sigma_transpose_empty_control.lp"
for name in internal_op_empty_reproducer internal_op_family_empty_reproducer sigma_hom_empty_reproducer; do
  sed 's/require open emdash.emdash3_2;/require open emdash.baseline_prefix;/' \
    "audits/$name.lp" > "$stage_root/audits/baseline_$name.lp"
done

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
expect_rejected() {
  local file="$1" pattern="$2"
  local log="$stage_root/logs/${file//\//_}.log"
  local rc=0
  timeout --signal=INT 90s lambdapi check -w --no-colors "$file" > "$log" 2>&1 || rc=$?
  if [[ "$rc" -ne 1 ]] || ! rg -q 'The proof is not finished:' "$log" || ! rg -q "$pattern" "$log"; then
    printf 'unexpected negative result (%s); inspect %s\n' "$rc" "$log" >&2
    return 1
  fi
  printf 'expected typed rejection: %s\n' "$file"
}

cd "$stage_root"
check_target baseline_prefix.lp
check_target emdash3_2.lp
for core in baseline_prefix emdash3_2; do
  python3 "$source_root/scripts/warning_summary.py" "$stage_root/logs/$core.lp.log" \
    --strict-parse > "$stage_root/logs/$core-warning-summary.txt"
  python3 "$source_root/scripts/audit_rule_lhs.py" "$stage_root/$core.lp" --strict \
    > "$stage_root/logs/$core-lhs-audit.txt"
done
check_target audits/total_op_basis_checks.lp -w
check_target audits/total_op_sigma_checks.lp -w
# Acceptance on the original prefix reproduces the defects; it is not a
# positive mathematical-library result. No unsafe witness enters the candidate.
for name in internal_op_empty_reproducer internal_op_family_empty_reproducer sigma_hom_empty_reproducer; do
  check_target "audits/baseline_$name.lp" -w
done
expect_rejected audits/internal_op_empty_reproducer.lp 'Cat_cat ≡ CoAbove2_cat Cat_cat'
expect_rejected audits/internal_op_family_empty_reproducer.lp 'Cat_cat ≡ CoAbove2_cat Cat_cat'
expect_rejected audits/sigma_transpose_empty_control.lp 'Sigma_cat.*≡.*Sigma_cat'
printf 'total-op prefix controls passed; complete kernel remains unqualified\n'
printf 'evidence retained in %s\n' "$stage_root"
