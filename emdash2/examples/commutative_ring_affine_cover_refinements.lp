/*
  Reviewer for executable refinements through affine-cover generators.

  A retained sieve member computes its existing Boolean-selected
  factorization.  The selected chart, whole affine realization, and coordinate
  ring are then derived from that side without storing another package.  The
  refinement itself is not asserted affine, and no external coherence or
  scheme condition is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_affine_cover_refinements;

// Literal Boolean chart selection computes at both generator branches.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryAffineCoverPresentation K P)) ⊢
  @binary_affine_cover_chart_at_side K P Q false
  ≡ sigma_Fst Q;

// The branch-indexed whole affine realization computes at a literal side.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryAffineCoverPresentation K P)) ⊢
  @binary_affine_cover_realization_at_side K P Q true
  ≡ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q)));

// Membership is consumed by the presentation's existing generation owner.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryAffineCoverPresentation K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (member : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      q)) ⊢
  @binary_affine_cover_refinement_at K P Q q member
  ≡ @binary_selected_cover_generation_at
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      (sigma_Fst (sigma_Snd (sigma_Snd Q)))
      q member;

// A left factorization selects the first retained chart.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryAffineCoverPresentation K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (factor0 : τ (@CoverChartFactorization
      K P (sigma_Fst Q) q)) ⊢
  @binary_affine_cover_refinement_chart
    K P Q q
    (@binary_cover_chart_factorization_left
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q factor0)
  ≡ sigma_Fst Q;

// A right factorization selects the second whole affine realization.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryAffineCoverPresentation K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (factor1 : τ (@CoverChartFactorization
      K P (sigma_Fst (sigma_Snd Q)) q)) ⊢
  @binary_affine_cover_refinement_realization
    K P Q q
    (@binary_cover_chart_factorization_right
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q factor1)
  ≡ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q)));

// Its selected coordinate ring is derived from that same retained branch.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryAffineCoverPresentation K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (factor1 : τ (@CoverChartFactorization
      K P (sigma_Fst (sigma_Snd Q)) q)) ⊢
  @binary_affine_cover_refinement_ring
    K P Q q
    (@binary_cover_chart_factorization_right
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q factor1)
  ≡ @affine_cover_chart_ring
      K P
      (sigma_Fst (sigma_Snd Q))
      (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q))));
