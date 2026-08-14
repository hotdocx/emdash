/*
  Focused reviewer for the transparent integer specialization of telescope
  localization. It checks the chosen representatives, executable shifts,
  equivalence packaging, and sethood without adding a new rewrite owner.
*/

require open emdash.emdash3_2_integer_localization;

assert ⊢ Integer_grpd : Grpd;

assert ⊢ integer_zero : τ Integer_grpd;

assert ⊢ integer_neg_one : τ Integer_grpd;

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

assert ⊢ integer_pred integer_zero
  ≡ integer_neg_one;

assert (n x : τ Nat_grpd) ⊢
  integer_stage_step n x
  : τ (@= Integer_grpd
      (integer_stage (succ n) (succ x))
      (integer_stage n x));

assert (z : τ Integer_grpd) ⊢
  integer_succ_pred z
  : τ (@= Integer_grpd (integer_succ (integer_pred z)) z);

assert (z : τ Integer_grpd) ⊢
  integer_pred_succ z
  : τ (@= Integer_grpd (integer_pred (integer_succ z)) z);

assert ⊢ integer_succ_omega_equiv
  : τ (@OmegaEquivAlong
      Grpd_cat Integer_grpd Integer_grpd integer_succ);

assert ⊢ integer_succ_equiv
  : τ (TypeEquiv Integer_grpd Integer_grpd);

assert ⊢ type_equiv_to integer_succ_equiv
  ≡ integer_succ;

assert (z : τ Integer_grpd) ⊢
  type_equiv_from integer_succ_equiv z
  ≡ integer_pred z;

assert ⊢ integer_succ_path
  : τ (@= Grpd_grpd Integer_grpd Integer_grpd);

assert (z : τ Integer_grpd) ⊢
  integer_succ_path_coe z
  : τ (@= Integer_grpd
      (@coe_grpd
        Integer_grpd Integer_grpd integer_succ_path z)
      (integer_succ z));

assert ⊢ integer_succ_neg_one
  : τ (@= Integer_grpd
      (integer_succ integer_neg_one)
      integer_zero);

assert (D : τ Integer_grpd → Grpd)
  (hD : Π z : τ Integer_grpd, τ (IsSetGrpd (D z)))
  (d : Π n : τ Nat_grpd,
    Π x : τ Nat_grpd,
      τ (D (integer_stage n x)))
  (coh : Π n : τ Nat_grpd,
    Π x : τ Nat_grpd,
      τ (@PathOver
        Integer_grpd D
        (integer_stage (succ n) (succ x))
        (integer_stage n x)
        (integer_stage_step n x)
        (d (succ n) (succ x))
        (d n x)))
  (n x : τ Nat_grpd) ⊢
  @integer_ind D hD d coh (integer_stage n x)
  ≡ d n x;

assert [B : Grpd]
  (hB : τ (IsSetGrpd B))
  (d : Π n : τ Nat_grpd, Π x : τ Nat_grpd, τ B)
  (coh : Π n : τ Nat_grpd,
    Π x : τ Nat_grpd,
      τ (@= B (d (succ n) (succ x)) (d n x)))
  (n x : τ Nat_grpd) ⊢
  @integer_elim B hB d coh (integer_stage n x)
  ≡ d n x;

assert ⊢ integer_is_set
  : τ (IsSetGrpd Integer_grpd);

// The HIT step is path data; successor and predecessor are not judgmentally
// inverse on an open representative.
assertnot (n x : τ Nat_grpd) ⊢
  integer_succ (integer_pred (integer_stage n x))
  ≡ integer_stage n x;
