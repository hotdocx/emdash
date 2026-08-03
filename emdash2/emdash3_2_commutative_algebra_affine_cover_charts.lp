/*
  Whole affine realizations of selected ringed-space cover charts.

  A selected chart of a global reflective ringed-space cover becomes affine
  only after retaining a supplied reflective presentation of its actual
  slice, a coordinate ring and affine-scheme presentation, a whole affine
  basis functor, and the existing whole AffineBasisRealizationAlong joining
  that basis to the ambient restriction.  The resulting coordinate DefIso is
  derived from that existing whole owner.

  Readable projections are exposed for consumers.  Dependent projection
  types deliberately retain their literal nested-Sigma endpoints instead of
  unfolding those endpoints through readable aliases; this is the stable
  package normal form and requires no package eta, rule, or unifier.  The
  transparent module adds no overlap, cocycle, locally-ringed, or scheme
  claim.
*/

require open emdash.emdash3_2_commutative_algebra_affine_basis;

// The supplied reflective presentation of the actual ambient chart slice.
symbol CoverChartSlicePresentation
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : Grpd
≔ @SuppliedReflectiveCommRingedSlicePresentation
    K
    (@reflective_comm_ringed_space_cover_ringed_site K P)
    (@reflective_comm_ringed_space_cover_chart_domain K P chart);

// A whole affine-basis functor from affine coordinates to the actual slice.
symbol CoverChartAffineBasisFunctor
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (R : τ CommRing)
  : Grpd
≔ @Functor
    (@AffineSpecBigSlice_cat R)
    (@Slice_cat K
      (@reflective_comm_ringed_space_cover_chart_domain K P chart));

// One whole semantic and computational affine realization of a cover chart.
symbol AffineCoverChartRealization
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : Grpd
≔ `Σ_ slice : τ (@CoverChartSlicePresentation K P chart),
   `Σ_ R : τ CommRing,
   `Σ_ affine : τ (@AffineSchemePresentation R),
   `Σ_ basis_func : τ (@CoverChartAffineBasisFunctor K P chart R),
      @AffineBasisRealizationAlong
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_chart_domain K P chart)
        slice R affine basis_func;

symbol affine_cover_chart_realization_intro
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (slice : τ (@CoverChartSlicePresentation K P chart))
  (R : τ CommRing)
  (affine : τ (@AffineSchemePresentation R))
  (basis_func : τ (@CoverChartAffineBasisFunctor K P chart R))
  (realization : τ (@AffineBasisRealizationAlong
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      slice R affine basis_func))
  : τ (@AffineCoverChartRealization K P chart)
≔ @Struct_sigma
    (@CoverChartSlicePresentation K P chart)
    (λ slice0 : τ (@CoverChartSlicePresentation K P chart),
      `Σ_ R0 : τ CommRing,
      `Σ_ affine0 : τ (@AffineSchemePresentation R0),
      `Σ_ basis_func0 : τ (@CoverChartAffineBasisFunctor
          K P chart R0),
        @AffineBasisRealizationAlong
          K
          (@reflective_comm_ringed_space_cover_ringed_site K P)
          (@reflective_comm_ringed_space_cover_chart_domain K P chart)
          slice0 R0 affine0 basis_func0)
    slice
    (@Struct_sigma
      CommRing
      (λ R0 : τ CommRing,
        `Σ_ affine0 : τ (@AffineSchemePresentation R0),
        `Σ_ basis_func0 : τ (@CoverChartAffineBasisFunctor
            K P chart R0),
          @AffineBasisRealizationAlong
            K
            (@reflective_comm_ringed_space_cover_ringed_site K P)
            (@reflective_comm_ringed_space_cover_chart_domain K P chart)
            slice R0 affine0 basis_func0)
      R
      (@Struct_sigma
        (@AffineSchemePresentation R)
        (λ affine0 : τ (@AffineSchemePresentation R),
          `Σ_ basis_func0 : τ (@CoverChartAffineBasisFunctor
              K P chart R),
            @AffineBasisRealizationAlong
              K
              (@reflective_comm_ringed_space_cover_ringed_site K P)
              (@reflective_comm_ringed_space_cover_chart_domain K P chart)
              slice R affine0 basis_func0)
        affine
        (@Struct_sigma
          (@CoverChartAffineBasisFunctor K P chart R)
          (λ basis_func0 : τ (@CoverChartAffineBasisFunctor
              K P chart R),
            @AffineBasisRealizationAlong
              K
              (@reflective_comm_ringed_space_cover_ringed_site K P)
              (@reflective_comm_ringed_space_cover_chart_domain K P chart)
              slice R affine basis_func0)
          basis_func realization)));

// Readable slice-presentation observation.
symbol affine_cover_chart_slice
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (Q : τ (@AffineCoverChartRealization K P chart))
  : τ (@CoverChartSlicePresentation K P chart)
≔ sigma_Fst Q;

// Readable coordinate-ring observation.
symbol affine_cover_chart_ring
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (Q : τ (@AffineCoverChartRealization K P chart))
  : τ CommRing
≔ sigma_Fst (sigma_Snd Q);

// Affine presentation at the literal retained coordinate-ring projection.
symbol affine_cover_chart_affine_scheme
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (Q : τ (@AffineCoverChartRealization K P chart))
  : τ (@AffineSchemePresentation (sigma_Fst (sigma_Snd Q)))
≔ sigma_Fst (sigma_Snd (sigma_Snd Q));

// Whole affine-basis functor at the literal retained ring projection.
symbol affine_cover_chart_basis_func
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (Q : τ (@AffineCoverChartRealization K P chart))
  : τ (@CoverChartAffineBasisFunctor
      K P chart (sigma_Fst (sigma_Snd Q)))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q)));

// The retained whole ambient-to-affine basis realization.
symbol affine_cover_chart_basis_realization
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (Q : τ (@AffineCoverChartRealization K P chart))
  : τ (@AffineBasisRealizationAlong
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q))
      (sigma_Fst (sigma_Snd (sigma_Snd Q)))
      (sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q)))))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q)));

// Derived whole DefIso from the ambient basis restriction to coordinates.
symbol affine_cover_chart_coordinate_defiso
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (Q : τ (@AffineCoverChartRealization K P chart))
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
        (sigma_Fst (sigma_Snd Q))))
≔ @affine_basis_realization_coordinate_defiso
    K
    (@reflective_comm_ringed_space_cover_ringed_site K P)
    (@reflective_comm_ringed_space_cover_chart_domain K P chart)
    (sigma_Fst Q)
    (sigma_Fst (sigma_Snd Q))
    (sigma_Fst (sigma_Snd (sigma_Snd Q)))
    (sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q))))
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q))));
