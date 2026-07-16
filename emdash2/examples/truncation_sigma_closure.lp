/*
  Reviewer milestone: same-level dependent-Sigma truncation closure.

  Both the base classifier and every fibre must be n-truncated. Contractible
  totals form the recursion base; successor paths use the existing
  base-path/fibre-PathOver Sigma view.
*/

require open emdash.emdash3_2;

assert (n : TruncLevel) ⊢
  SigmaTruncClosure n
  : Grpd;

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd n A))
  (hB : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_sigma n A B hA hB
  : τ (IsTruncGrpd n (@Σ_ A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsContr A))
  (hB : Π x : τ A, τ (IsContr (B x))) ⊢
  @is_trunc_sigma trunc_minus_two A B hA hB
  ≡ @is_contr_sigma A B hA hB;

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x))) ⊢
  @is_trunc_sigma (trunc_succ n) A B hA hB
  ≡ @trunc_sigma_succ
      n
      (@is_trunc_sigma n)
      A
      B
      hA
      hB;

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsPropGrpd A))
  (hB : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_trunc_sigma trunc_minus_one A B hA hB
  : τ (IsPropGrpd (@Σ_ A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsSetGrpd A))
  (hB : Π x : τ A, τ (IsSetGrpd (B x))) ⊢
  @is_trunc_sigma trunc_zero A B hA hB
  : τ (IsSetGrpd (@Σ_ A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsGroupoidGrpd A))
  (hB : Π x : τ A, τ (IsGroupoidGrpd (B x))) ⊢
  @is_trunc_sigma trunc_one A B hA hB
  : τ (IsGroupoidGrpd (@Σ_ A B));

assert (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x)))
  (u v : @τΣ_ A B) ⊢
  @is_trunc_sigma (trunc_succ n) A B hA hB u v
  : τ (IsTruncGrpd n (@= (@Σ_ A B) u v));

// Neither hypothesis is erased by the stable theorem head.
assertnot (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA kA : τ (IsTruncGrpd n A))
  (hB : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_sigma n A B hA hB
  ≡ @is_trunc_sigma n A B kA hB;

assertnot (n : TruncLevel)
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsTruncGrpd n A))
  (hB kB : Π x : τ A, τ (IsTruncGrpd n (B x))) ⊢
  @is_trunc_sigma n A B hA hB
  ≡ @is_trunc_sigma n A B hA kB;
