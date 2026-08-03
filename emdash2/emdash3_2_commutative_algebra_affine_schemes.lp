/*
  Thin assumption-explicit computational affine-scheme presentations.

  The base ring already determines the conventional big affine slice and its
  internally generated Zariski topology. A presentation therefore retains
  only the two genuinely supplied capabilities: a whole reflective structure
  sheaf presentation and whole coordinate-localization locality.

  All chart, restriction, localization, matching, and overlap action remains
  at existing functorial and structured-ring owners. Selected finite atlases
  are consumer data rather than duplicate record fields. This transparent
  module adds no rules and does not construct sheafification or locality,
  define general non-affine gluing, compare with a small site, construct
  stalks, or assert a stalk-local-ring theorem.
*/

require open emdash.emdash3_2_commutative_algebra_affine_ringed_sites;
require open emdash.emdash3_2_commutative_algebra_affine_locality;

// Whole computational presentation of the affine scheme associated to R.
symbol AffineSchemePresentation
  (R : τ CommRing)
  : Grpd
≔ `Σ_ structure : τ (@AffineStructureSheafPresentation R),
    @AffineCoordinateLocalizationLocality R;

// Constructor for the transparent two-field presentation.
symbol affine_scheme_intro
  [R : τ CommRing]
  (structure : τ (@AffineStructureSheafPresentation R))
  (locality : τ (@AffineCoordinateLocalizationLocality R))
  : τ (@AffineSchemePresentation R)
≔ @Struct_sigma
    (@AffineStructureSheafPresentation R)
    (λ _ : τ (@AffineStructureSheafPresentation R),
      @AffineCoordinateLocalizationLocality R)
    structure locality;

// Selected whole reflective structure-sheaf presentation.
symbol affine_scheme_structure
  [R : τ CommRing]
  (X : τ (@AffineSchemePresentation R))
  : τ (@AffineStructureSheafPresentation R)
≔ sigma_Fst X;

// Selected whole coordinate-localization locality capability.
symbol affine_scheme_locality
  [R : τ CommRing]
  (X : τ (@AffineSchemePresentation R))
  : τ (@AffineCoordinateLocalizationLocality R)
≔ sigma_Snd X;

// Reflective ringed site on the exact internally generated big-Zariski site.
symbol affine_scheme_ringed_site
  [R : τ CommRing]
  (X : τ (@AffineSchemePresentation R))
  : τ (@ReflectiveCommRingedSite (@AffineSpecBigSlice_cat R))
≔ @affine_structure_sheaf_ringed_site
    R (@affine_scheme_structure R X);

// Underlying whole structure presheaf of the selected reflective ringed site.
symbol affine_scheme_underlying_psh
  [R : τ CommRing]
  (X : τ (@AffineSchemePresentation R))
  : τ (@CommRingPsh (@AffineSpecBigSlice_cat R))
≔ @affine_structure_sheaf_underlying_psh
    R (@affine_scheme_structure R X);

// Whole computational presentation by the coordinate-ring presheaf.
symbol affine_scheme_coordinate_defiso
  [R : τ CommRing]
  (X : τ (@AffineSchemePresentation R))
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_scheme_underlying_psh R X)
      (@affine_spec_coordinate_psh R))
≔ @affine_structure_sheaf_coordinate_defiso
    R (@affine_scheme_structure R X);

// Whole localization locality at one chart, section, and selected package.
symbol affine_scheme_locality_at
  [R : τ CommRing]
  (X : τ (@AffineSchemePresentation R))
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
≔ @affine_coordinate_localization_locality_at
    R (@affine_scheme_locality R X)
    U s localization;
