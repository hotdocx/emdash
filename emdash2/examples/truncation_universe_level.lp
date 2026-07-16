/*
  Reviewer milestone: the expected level of truncated classifier universes.

  TypeEquiv(A,B) is n-truncated when both endpoints are n-truncated. The
  contractible base uses an explicit constant inverse; successor levels use
  Pi/Sigma closure and proposition-valued equivalence evidence. Restricted
  package univalence then proves that TruncGrpdU(n) is (n+1)-truncated.
*/

require open emdash.emdash3_2;

assert [A B : Grpd]
  (f : τ A → τ B) ⊢
  @is_equiv_map_evidence_is_prop A B f
  : τ (IsPropGrpd (@IsEquivMap A B f));

assert [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B)) ⊢
  @contractible_type_equiv A B hA hB
  : τ (IsContr (TypeEquiv A B));

assert (n : TruncLevel) ⊢
  @is_trunc_type_equiv n
  : τ (TypeEquivTruncClosure n);

assert [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B)) ⊢
  @is_trunc_type_equiv trunc_minus_two A B hA hB
  ≡ @contractible_type_equiv A B hA hB;

assert (n : TruncLevel)
  [A B : Grpd]
  (hB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @trunc_type_equiv_succ n A B hB
  : τ (IsTruncGrpd (trunc_succ n) (TypeEquiv A B));

assert (n : TruncLevel)
  [A B : Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @is_trunc_type_equiv (trunc_succ n) A B hA hB
  ≡ @trunc_type_equiv_succ n A B hB;

// Source evidence is irrelevant after the contractible base.
assert (n : TruncLevel)
  [A B : Grpd]
  (hA kA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @is_trunc_type_equiv (trunc_succ n) A B hA hB
  ≡ @is_trunc_type_equiv (trunc_succ n) A B kA hB;

assert (n : TruncLevel) ⊢
  @is_trunc_grpd_universe n
  : τ (IsTruncGrpd
      (trunc_succ n)
      (TruncGrpdU n));

assert ⊢
  @is_trunc_grpd_universe trunc_minus_two
  : τ (IsPropGrpd (TruncGrpdU trunc_minus_two));

assert ⊢
  @is_trunc_grpd_universe trunc_minus_one
  : τ (IsSetGrpd PropU_grpd);

assert ⊢
  @is_trunc_grpd_universe trunc_zero
  : τ (IsGroupoidGrpd SetU_grpd);

// Base source evidence and successor target evidence remain explicit data.
assertnot [A B : Grpd]
  (hA kA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B) ⊢
  @contractible_map_is_equiv A B hA hB f
  ≡ @contractible_map_is_equiv A B kA hB f;

assertnot (n : TruncLevel)
  [A B : Grpd]
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB kB : τ (IsTruncGrpd (trunc_succ n) B)) ⊢
  @is_trunc_type_equiv (trunc_succ n) A B hA hB
  ≡ @is_trunc_type_equiv (trunc_succ n) A B hA kB;

// No same-level package-universe theorem is installed.
assertnot (n : TruncLevel) ⊢
  @is_trunc_grpd_universe n
  : τ (IsTruncGrpd n (TruncGrpdU n));
