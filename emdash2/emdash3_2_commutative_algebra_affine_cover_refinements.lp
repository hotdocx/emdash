/*
  Executable refinements through selected affine-cover generators.

  A BinaryAffineCoverPresentation already retains two affine generators and,
  for every arrow of its covering sieve, a Boolean-selected factorization
  through one of them.  This module exposes the direct consumer route from a
  sieve member to that factorization, the selected chart, its already-owned
  whole affine realization, and its coordinate ring.

  No second refinement record is introduced: the factorization owns the
  Boolean side, while the presentation already owns both realizations.
  Realizations therefore remain in their canonical branch-indexed Bool family
  rather than relying on a dependent fusion through the readable selected-
  chart observation.  The arbitrary sieve member is a refinement of an
  affine generator; it is not itself asserted affine.  This transparent
  module adds no rule, unifier, external coherence, or scheme claim.
*/

require open emdash.emdash3_2_commutative_algebra_affine_cover_presentations;

// Readable selection of one retained chart from the executable Boolean side.
symbol binary_affine_cover_chart_at_side
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  (side : τ Bool_grpd)
  : τ (@ReflectiveCommRingedSpaceCoverChart K P)
≔ @bool_elim
    (λ _ : τ Bool_grpd, @ReflectiveCommRingedSpaceCoverChart K P)
    (sigma_Fst Q)
    (sigma_Fst (sigma_Snd Q))
    side;

// The already-retained whole affine realization selected by that side.
symbol binary_affine_cover_realization_at_side
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  (side : τ Bool_grpd)
  : τ (@bool_elim
      (λ _ : τ Bool_grpd, Grpd_grpd)
      (@AffineCoverChartRealization K P (sigma_Fst Q))
      (@AffineCoverChartRealization K P (sigma_Fst (sigma_Snd Q)))
      side)
≔ @bool_elim
    (λ side0 : τ Bool_grpd,
      @bool_elim
        (λ _ : τ Bool_grpd, Grpd_grpd)
        (@AffineCoverChartRealization K P (sigma_Fst Q))
        (@AffineCoverChartRealization K P (sigma_Fst (sigma_Snd Q)))
        side0)
    (sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q))))
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q))))
    side;

// Every retained sieve member computes its selected chart factorization.
symbol binary_affine_cover_refinement_at
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (member : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      q))
  : τ (@BinaryCoverChartFactorization
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q)
≔ @binary_selected_cover_generation_at
    K P
    (sigma_Fst Q)
    (sigma_Fst (sigma_Snd Q))
    (sigma_Fst (sigma_Snd (sigma_Snd Q)))
    q member;

// Readable selected generator for one already-computed refinement.
symbol binary_affine_cover_refinement_chart
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [Q : τ (@BinaryAffineCoverPresentation K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@BinaryCoverChartFactorization
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q))
  : τ (@ReflectiveCommRingedSpaceCoverChart K P)
≔ @binary_affine_cover_chart_at_side
    K P Q
    (@binary_cover_chart_factorization_side
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q factor);

// Whole affine realization selected in the canonical branch-indexed family.
symbol binary_affine_cover_refinement_realization
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [Q : τ (@BinaryAffineCoverPresentation K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@BinaryCoverChartFactorization
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q))
  : τ (@bool_elim
      (λ _ : τ Bool_grpd, Grpd_grpd)
      (@AffineCoverChartRealization K P (sigma_Fst Q))
      (@AffineCoverChartRealization K P (sigma_Fst (sigma_Snd Q)))
      (@binary_cover_chart_factorization_side
        K P
        (sigma_Fst Q)
        (sigma_Fst (sigma_Snd Q))
        q factor))
≔ @binary_affine_cover_realization_at_side
    K P Q
    (@binary_cover_chart_factorization_side
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q factor);

// Coordinate ring of the selected affine generator.
symbol binary_affine_cover_refinement_ring
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [Q : τ (@BinaryAffineCoverPresentation K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@BinaryCoverChartFactorization
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q))
  : τ CommRing
≔ @bool_elim
    (λ _ : τ Bool_grpd, CommRing)
    (@affine_cover_chart_ring
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q)))))
    (@affine_cover_chart_ring
      K P
      (sigma_Fst (sigma_Snd Q))
      (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q)))))
    (@binary_cover_chart_factorization_side
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      q factor);
