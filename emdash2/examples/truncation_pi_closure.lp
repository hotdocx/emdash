/* Reviewer example: dependent Pi preserves every native truncation level. */

require open emdash.emdash3_2;

assert (n : TruncLevel) ⊢
  PiTruncClosure n
  : Grpd;

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_pi n A B h
  : τ (IsTruncGrpd n (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsContr (B x))) ⊢
  @is_trunc_pi trunc_minus_two A B h
  ≡ @is_contr_pi A B h;

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x))) ⊢
  @is_trunc_pi (trunc_succ n) A B h
  ≡ @trunc_pi_succ
      n
      (@is_trunc_pi n)
      A
      B
      h;

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_trunc_pi trunc_minus_one A B h
  : τ (IsPropGrpd (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsSetGrpd (B x))) ⊢
  @is_trunc_pi trunc_zero A B h
  : τ (IsSetGrpd (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsGroupoidGrpd (B x))) ⊢
  @is_trunc_pi trunc_one A B h
  : τ (IsGroupoidGrpd (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_prop_pi A B h
  ≡ @is_trunc_pi trunc_minus_one A B h;

assertnot (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (h k : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_pi n A B h
  ≡ @is_trunc_pi n A B k;
