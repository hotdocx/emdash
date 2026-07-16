/*
  Reviewer milestone: homotopy-truncation evidence is invariant under an
  ordinary TypeEquiv through the canonical groupoid-univalence decoder.

  This does not yet claim categorical/OmegaEquiv invariance, monotonicity,
  Pi/Sigma closure, or the recursive IsNCat object-truncation theorem.
*/

require open emdash.emdash3_2;

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @is_trunc_grpd_type_equiv n A B e
  : τ (TypeEquiv (IsTruncGrpd n A) (IsTruncGrpd n B));

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_equiv_to n A B e h
  : τ (IsTruncGrpd n B);

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n B)) ⊢
  @is_trunc_grpd_equiv_from n A B e h
  : τ (IsTruncGrpd n A);

assert (n : TruncLevel)
  [A : Grpd] ⊢
  @is_trunc_grpd_type_equiv n A A (@type_equiv_refl A)
  ≡ @type_equiv_refl (IsTruncGrpd n A);

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_equiv_to n A A (@type_equiv_refl A) h
  ≡ h;

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n B)) ⊢
  type_equiv_right (@is_trunc_grpd_type_equiv n A B e) h
  : τ (
      @is_trunc_grpd_equiv_to n A B e
        (@is_trunc_grpd_equiv_from n A B e h)
      = h);

assert (n : TruncLevel)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n A)) ⊢
  type_equiv_left (@is_trunc_grpd_type_equiv n A B e) h
  : τ (
      @is_trunc_grpd_equiv_from n A B e
        (@is_trunc_grpd_equiv_to n A B e h)
      = h);

// Open self-equivalences are not silently reflexive runtime packages/maps.
assertnot (n : TruncLevel)
  [A : Grpd]
  (e : τ (TypeEquiv A A)) ⊢
  @is_trunc_grpd_type_equiv n A A e
  ≡ @type_equiv_refl (IsTruncGrpd n A);

assertnot (n : TruncLevel)
  [A : Grpd]
  (e : τ (TypeEquiv A A))
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_equiv_to n A A e h
  ≡ h;
