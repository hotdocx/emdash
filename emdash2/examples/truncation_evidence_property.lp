/*
  Reviewer example: truncation evidence is proposition-valued.

  Contractibility witnesses are compared through the active dependent Sigma
  path view, proposition-valued dependent products use Pi happly/funext, and a
  stable recursive owner exposes bounded base/successor computation.
*/

require open emdash.emdash3_2;

assert [A : Grpd]
  (c d : τ (IsContr A)) ⊢
  @is_contr_evidence_path A c d
  : τ (@= (IsContr A) c d);

assert [A : Grpd] ⊢
  @is_contr_evidence_is_prop A
  : τ (IsPropGrpd (IsContr A));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsContr (B x))) ⊢
  @is_contr_pi A B h
  : τ (IsContr (@Pi_grpd A B));

assert [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsPropGrpd (B x))) ⊢
  @is_prop_pi A B h
  : τ (IsPropGrpd (@Pi_grpd A B));

assert (n : TruncLevel)
  [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop n A
  : τ (IsPropGrpd (IsTruncGrpd n A));

assert [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop trunc_minus_two A
  ≡ @is_contr_evidence_is_prop A;

assert (n : TruncLevel)
  [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop (trunc_succ n) A
  ≡ @trunc_evidence_prop_succ
      n
      (@is_trunc_grpd_evidence_is_prop n)
      A;

assert [A : Grpd] ⊢
  @is_trunc_grpd_evidence_is_prop trunc_zero A
  : τ (IsPropGrpd (IsSetGrpd A));

assertnot [A : Grpd]
  (c : τ (IsContr A)) ⊢
  @is_contr_evidence_path A c c
  ≡ @eq_refl (IsContr A) c;

assertnot (n : TruncLevel)
  [A : Grpd]
  (h k : τ (IsTruncGrpd n A)) ⊢
  h ≡ k;
