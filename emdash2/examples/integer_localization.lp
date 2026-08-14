/*
  Focused reviewer for the transparent integer specialization of telescope
  localization. It checks the chosen representatives, executable shifts,
  equivalence packaging, and sethood without adding a new rewrite owner.
*/

require open emdash.emdash3_2_integer_localization;

assert ⊢ Integer_grpd : Grpd;

assert ⊢ integer_zero : τ Integer_grpd;

assert (n : τ Nat_grpd) ⊢
  integer_of_nat n : τ Integer_grpd;

assert (n x : τ Nat_grpd) ⊢
  integer_succ (integer_stage n x)
  ≡ integer_stage n (succ x);

assert (n x : τ Nat_grpd) ⊢
  integer_pred (integer_stage n x)
  ≡ integer_stage (succ n) x;

assert (n : τ Nat_grpd) ⊢
  integer_succ (integer_of_nat n)
  ≡ integer_of_nat (succ n);

assert ⊢ integer_succ_omega_equiv
  : τ (@OmegaEquivAlong
      Grpd_cat Integer_grpd Integer_grpd integer_succ);

assert ⊢ integer_succ_equiv
  : τ (TypeEquiv Integer_grpd Integer_grpd);

assert ⊢ type_equiv_to integer_succ_equiv
  ≡ integer_succ;

assert ⊢ integer_is_set
  : τ (IsSetGrpd Integer_grpd);

// The HIT step is path data; successor and predecessor are not judgmentally
// inverse on an open representative.
assertnot (n x : τ Nat_grpd) ⊢
  integer_succ (integer_pred (integer_stage n x))
  ≡ integer_stage n x;
