/*
  Assumption-explicit whole localization locality for affine coordinates.

  For every object U of the computational big affine slice, every coordinate
  section s in O_coord(U), and every supplied universal-property localization
  at s, this capability requires the existing restriction functor into
  internally coherent matching families over D(s) to be an
  OmegaEquivAlong in Cat_cat. Its selected inverse is therefore a whole glue
  functor with both whole composite-functor laws.

  Literal charts reduce the coordinate value to their retained ring, so the
  specialization remains computational. D(s) need not cover U: this is
  Cartier/Zeuner localization locality, not ordinary covering-sieve sheaf
  descent or a stalk-local-ring condition. The transparent module adds no
  rules, external naturality fields, global localization choice, small-site
  comparison, or scheme package.
*/

require open emdash.emdash3_2_commutative_algebra_affine_spec;
require open emdash.emdash3_2_commutative_algebra_glue;

// Whole coordinate-locality capability over every selected affine localization.
symbol AffineCoordinateLocalizationLocality
  (R : τ CommRing)
  : Grpd
≔ @Pi_grpd
    (Obj (@AffineSpecBigSlice_cat R))
    (λ U : τ (Obj (@AffineSpecBigSlice_cat R)),
      @Pi_grpd
        (@CommRingPshSection
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_coordinate_psh R)
          U)
        (λ s : τ (@CommRingPshSection
            (@AffineSpecBigSlice_cat R)
            (@affine_spec_coordinate_psh R)
            U),
          @Pi_grpd
            (@CommRingLocalizationAt
              (@comm_ring_psh_value
                (@AffineSpecBigSlice_cat R)
                (@affine_spec_coordinate_psh R)
                U)
              s)
            (λ localization : τ (@CommRingLocalizationAt
                (@comm_ring_psh_value
                  (@AffineSpecBigSlice_cat R)
                  (@affine_spec_coordinate_psh R)
                  U)
                s),
              @CommRingPshLocalizationLocality
                (@AffineSpecBigSlice_cat R)
                (@affine_spec_coordinate_psh R)
                U s localization)));

// Selected whole locality at one chart, section, and localization package.
symbol affine_coordinate_localization_locality_at
  [R : τ CommRing]
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
      s))
  : τ (@CommRingPshLocalizationLocality
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_coordinate_psh R)
      U s localization)
≔ locality U s localization;

// Compatibility view of affine whole locality through the earlier glue package.
symbol affine_coordinate_localization_legacy_glue
  [R : τ CommRing]
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
      s))
  : τ (@CommRingPshLocalizationGlue
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_coordinate_psh R)
      U s localization)
≔ @comm_ring_psh_localization_locality_legacy_glue
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    U s localization
    (@affine_coordinate_localization_locality_at
      R locality U s localization);
