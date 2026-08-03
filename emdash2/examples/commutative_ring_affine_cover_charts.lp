/*
  Reviewer for whole affine realizations of selected cover charts.

  A literal chart realization exposes its supplied reflective slice,
  coordinate ring, affine presentation, whole basis functor, and whole
  ambient-to-affine realization.  The derived coordinate comparison is one
  existing whole DefIso.  Canonical Sigma endpoints avoid package eta; no
  external coherence, local-ring condition, or scheme claim is used.
*/

require open emdash.emdash3_2_commutative_algebra_affine_cover_charts;

// A literal affine-chart realization exposes its selected coordinate ring.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (slice : τ (@CoverChartSlicePresentation K P chart))
  (R : τ CommRing)
  (affine : τ (@AffineSchemePresentation R))
  (basis_func : τ (@CoverChartAffineBasisFunctor K P chart R))
  (realization : τ (@AffineBasisRealizationAlong
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      slice R affine basis_func)) ⊢
  @affine_cover_chart_ring
    K P chart
    (@affine_cover_chart_realization_intro
      K P chart slice R affine basis_func realization)
  ≡ R;

// Remaining dependent observations use the canonical packaged endpoints.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (Q : τ (@AffineCoverChartRealization K P chart)) ⊢
  @affine_cover_chart_slice K P chart Q
  : τ (@CoverChartSlicePresentation K P chart);

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (Q : τ (@AffineCoverChartRealization K P chart)) ⊢
  @affine_cover_chart_affine_scheme K P chart Q
  : τ (@AffineSchemePresentation (sigma_Fst (sigma_Snd Q)));

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (Q : τ (@AffineCoverChartRealization K P chart)) ⊢
  @affine_cover_chart_basis_func K P chart Q
  : τ (@CoverChartAffineBasisFunctor
      K P chart (sigma_Fst (sigma_Snd Q)));

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (Q : τ (@AffineCoverChartRealization K P chart)) ⊢
  @affine_cover_chart_basis_realization K P chart Q
  : τ (@AffineBasisRealizationAlong
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      (sigma_Fst (sigma_Snd (sigma_Snd Q)))
      (sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q)))));

// Coordinates are related by the existing whole composed DefIso.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (Q : τ (@AffineCoverChartRealization K P chart)) ⊢
  @affine_cover_chart_coordinate_defiso K P chart Q
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat
        (sigma_Fst (sigma_Snd Q))))
      (@ambient_affine_basis_psh
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_chart_domain K P chart)
        (sigma_Fst (sigma_Snd Q))
        (sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q)))))
      (@affine_spec_coordinate_psh
        (sigma_Fst (sigma_Snd Q))));
