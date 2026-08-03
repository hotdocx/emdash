/*
  Reviewer for whole affine coordinate localization locality.

  The capability is supplied explicitly. These checks verify its dependent
  projection, exact literal-chart endpoints, both internal composite-functor
  laws, and the compatibility view through the earlier component-level glue
  package. No assertion constructs universal locality, covering-sieve descent,
  a stalk-local-ring structure, or a scheme.
*/

require open emdash.emdash3_2_commutative_algebra_affine_locality;

// The dependent capability projects at every retained localization package.
assert [R : τ CommRing]
  (locality : τ (@AffineCoordinateLocalizationLocality R))
  [U : τ (Obj (@AffineSpecBigSlice_cat R))]
  (s : τ (@CommRingPshSection
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_coordinate_psh R)
      U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_coordinate_psh R)
        U)
      s)) ⊢
  @affine_coordinate_localization_locality_at
    R locality U s localization
  : τ (@CommRingPshLocalizationLocality
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_coordinate_psh R)
      U s localization);

// At a literal chart R -> S, the localization carrier endpoint is S[1/s].
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (s : τ (@comm_ring_carrier S))
  (localization : τ (@CommRingLocalizationAt S s))
  (locality : τ (@AffineCoordinateLocalizationLocality R)) ⊢
  @affine_coordinate_localization_locality_at
    R locality (@affine_spec_chart R S h) s localization
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@comm_ring_carrier
        (@comm_ring_localization_target S s localization)))
      (@CommRingPshLocalizationMatching_cat
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_coordinate_psh R)
        (@affine_spec_chart R S h)
        s)
      (@comm_ring_psh_localization_matching_restriction_func
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_coordinate_psh R)
        (@affine_spec_chart R S h)
        s localization));

// The selected affine glue cancels restriction as a whole functor.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (s : τ (@comm_ring_carrier S))
  (localization : τ (@CommRingLocalizationAt S s))
  (locality : τ (@AffineCoordinateLocalizationLocality R)) ⊢
  @comm_ring_psh_localization_locality_glue_restrict_functor_path
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_chart R S h)
    s localization
    (@affine_coordinate_localization_locality_at
      R locality (@affine_spec_chart R S h) s localization)
  : τ (@=
      (Obj (Functor_cat
        (Path_cat (@comm_ring_carrier
          (@comm_ring_localization_target S s localization)))
        (Path_cat (@comm_ring_carrier
          (@comm_ring_localization_target S s localization)))))
      (@comp_cat_fapp0
        (Path_cat (@comm_ring_carrier
          (@comm_ring_localization_target S s localization)))
        (@CommRingPshLocalizationMatching_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s)
        (Path_cat (@comm_ring_carrier
          (@comm_ring_localization_target S s localization)))
        (@comm_ring_psh_localization_locality_glue_func
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s localization
          (@affine_coordinate_localization_locality_at
            R locality (@affine_spec_chart R S h) s localization))
        (@comm_ring_psh_localization_matching_restriction_func
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s localization))
      (@id_func (Path_cat (@comm_ring_carrier
        (@comm_ring_localization_target S s localization)))));

// Restriction after that same glue is identity on whole matching functors.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (s : τ (@comm_ring_carrier S))
  (localization : τ (@CommRingLocalizationAt S s))
  (locality : τ (@AffineCoordinateLocalizationLocality R)) ⊢
  @comm_ring_psh_localization_locality_restrict_glue_functor_path
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_chart R S h)
    s localization
    (@affine_coordinate_localization_locality_at
      R locality (@affine_spec_chart R S h) s localization)
  : τ (@=
      (Obj (Functor_cat
        (@CommRingPshLocalizationMatching_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s)
        (@CommRingPshLocalizationMatching_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s)))
      (@comp_cat_fapp0
        (@CommRingPshLocalizationMatching_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s)
        (Path_cat (@comm_ring_carrier
          (@comm_ring_localization_target S s localization)))
        (@CommRingPshLocalizationMatching_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s)
        (@comm_ring_psh_localization_matching_restriction_func
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s localization)
        (@comm_ring_psh_localization_locality_glue_func
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s localization
          (@affine_coordinate_localization_locality_at
            R locality (@affine_spec_chart R S h) s localization)))
      (@id_func
        (@CommRingPshLocalizationMatching_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          (@affine_spec_chart R S h)
          s)));

// The affine capability still serves existing component-view glue consumers.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (s : τ (@comm_ring_carrier S))
  (localization : τ (@CommRingLocalizationAt S s))
  (locality : τ (@AffineCoordinateLocalizationLocality R)) ⊢
  @affine_coordinate_localization_legacy_glue
    R locality (@affine_spec_chart R S h) s localization
  : τ (@CommRingPshLocalizationGlue
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_coordinate_psh R)
      (@affine_spec_chart R S h)
      s localization);
