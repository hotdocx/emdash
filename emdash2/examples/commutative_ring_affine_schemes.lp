/*
  Reviewer for the thin computational affine-scheme presentation.

  The closed base ring is F2 x F2. Its reflective structure-sheaf
  presentation and whole localization locality remain visibly supplied
  assumptions. The generated topology, whole coordinate comparison,
  complementary-idempotent cover, selected chart rings, whole restrictions,
  and zero overlap all route to existing computing owners.

  This is an assumption-explicit affine MVP, not constructed sheafification
  or locality, a general non-affine gluing theorem, a small-site comparison,
  or a stalk-local-ring theorem.
*/

require open emdash.emdash3_2_commutative_algebra_affine_schemes;
require open emdash.emdash3_2_commutative_algebra_affine_atlas;

// First closed-base presentation; only the two named capabilities are inputs.
symbol f2_split_affine_scheme
  (structure : τ (@AffineStructureSheafPresentation f2_split_comm_ring))
  (locality : τ (@AffineCoordinateLocalizationLocality f2_split_comm_ring))
  : τ (@AffineSchemePresentation f2_split_comm_ring)
≔ @affine_scheme_intro f2_split_comm_ring structure locality;

// The transparent record has exact beta at both primitive projections.
assert
  (structure : τ (@AffineStructureSheafPresentation f2_split_comm_ring))
  (locality : τ (@AffineCoordinateLocalizationLocality f2_split_comm_ring)) ⊢
  @affine_scheme_structure
    f2_split_comm_ring
    (@f2_split_affine_scheme structure locality)
  ≡ structure;

assert
  (structure : τ (@AffineStructureSheafPresentation f2_split_comm_ring))
  (locality : τ (@AffineCoordinateLocalizationLocality f2_split_comm_ring)) ⊢
  @affine_scheme_locality
    f2_split_comm_ring
    (@f2_split_affine_scheme structure locality)
  ≡ locality;

// The selected ringed site uses the exact internally generated topology.
assert
  (structure : τ (@AffineStructureSheafPresentation f2_split_comm_ring))
  (locality : τ (@AffineCoordinateLocalizationLocality f2_split_comm_ring)) ⊢
  @reflective_comm_ringed_site_topology
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_scheme_ringed_site
      f2_split_comm_ring
      (@f2_split_affine_scheme structure locality))
  ≡ @affine_spec_big_zariski_topology f2_split_comm_ring;

// The included structure sheaf has a whole DefIso to computing coordinates.
assert
  (structure : τ (@AffineStructureSheafPresentation f2_split_comm_ring))
  (locality : τ (@AffineCoordinateLocalizationLocality f2_split_comm_ring)) ⊢
  @affine_scheme_coordinate_defiso
    f2_split_comm_ring
    (@f2_split_affine_scheme structure locality)
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat f2_split_comm_ring))
      (@affine_structure_sheaf_underlying_psh
        f2_split_comm_ring structure)
      (@affine_spec_coordinate_psh f2_split_comm_ring));

// Generic DefIso cancellation remains equality of whole presheaf maps.
assert
  (structure : τ (@AffineStructureSheafPresentation f2_split_comm_ring))
  (locality : τ (@AffineCoordinateLocalizationLocality f2_split_comm_ring)) ⊢
  @comp_fapp0
    (@CommRingPsh_cat (@AffineSpecBigSlice_cat f2_split_comm_ring))
    (@affine_scheme_underlying_psh
      f2_split_comm_ring
      (@f2_split_affine_scheme structure locality))
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    (@affine_scheme_underlying_psh
      f2_split_comm_ring
      (@f2_split_affine_scheme structure locality))
    (@defiso_from
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat f2_split_comm_ring))
      (@affine_scheme_underlying_psh
        f2_split_comm_ring
        (@f2_split_affine_scheme structure locality))
      (@affine_spec_coordinate_psh f2_split_comm_ring)
      (@affine_scheme_coordinate_defiso
        f2_split_comm_ring
        (@f2_split_affine_scheme structure locality)))
    (@defiso_to
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat f2_split_comm_ring))
      (@affine_scheme_underlying_psh
        f2_split_comm_ring
        (@f2_split_affine_scheme structure locality))
      (@affine_spec_coordinate_psh f2_split_comm_ring)
      (@affine_scheme_coordinate_defiso
        f2_split_comm_ring
        (@f2_split_affine_scheme structure locality)))
  ≡ @id
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat f2_split_comm_ring))
      (@affine_scheme_underlying_psh
        f2_split_comm_ring
        (@f2_split_affine_scheme structure locality));

// The whole-chart coordinate ring computes literally to F2 x F2.
assert ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    (@affine_spec_whole_chart f2_split_comm_ring)
  ≡ f2_split_comm_ring;

// Whole locality projects at the split idempotent on that whole chart.
assert
  (structure : τ (@AffineStructureSheafPresentation f2_split_comm_ring))
  (locality : τ (@AffineCoordinateLocalizationLocality f2_split_comm_ring)) ⊢
  @affine_scheme_locality_at
    f2_split_comm_ring
    (@f2_split_affine_scheme structure locality)
    (@affine_spec_whole_chart f2_split_comm_ring)
    f2_split_idempotent
    f2_split_idempotent_localization
  : τ (@CommRingPshLocalizationLocality
      (@AffineSpecBigSlice_cat f2_split_comm_ring)
      (@affine_spec_coordinate_psh f2_split_comm_ring)
      (@affine_spec_whole_chart f2_split_comm_ring)
      f2_split_idempotent
      f2_split_idempotent_localization);

// The existing complementary idempotents give a concrete two-chart cover.
assert ⊢
  f2_split_cosplit_zariski_cover_family
  : τ (@CommRingZariskiCoverFamily f2_split_comm_ring);

assert ⊢
  @comm_ring_zariski_cover_family_length
    f2_split_comm_ring
    f2_split_cosplit_zariski_cover_family
  ≡ succ (succ zero);

// Both chart values are the selected fixed-image localization rings.
assert ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    (@affine_spec_product_split_chart f2_comm_ring f2_comm_ring)
  ≡ @comm_ring_localization_target
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_localization;

assert ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    (@affine_spec_product_cosplit_chart f2_comm_ring f2_comm_ring)
  ≡ @comm_ring_localization_target
      f2_split_comm_ring
      f2_split_cosplit_idempotent
      f2_split_cosplit_idempotent_localization;

// Orthogonality makes the overlap ring and both restrictions compute.
assert ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    f2_split_cosplit_overlap_chart
  ≡ zero_comm_ring;

assert ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    f2_split_cosplit_overlap_chart
    (@affine_spec_product_split_chart f2_comm_ring f2_comm_ring)
    (@affine_spec_product_split_overlap_chart_arrow
      f2_comm_ring f2_comm_ring)
  ≡ @comm_ring_hom_to_zero
      (@comm_ring_localization_target
        f2_split_comm_ring
        f2_split_idempotent
        f2_split_idempotent_localization);

assert ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    f2_split_cosplit_overlap_chart
    (@affine_spec_product_cosplit_chart f2_comm_ring f2_comm_ring)
    (@affine_spec_product_cosplit_overlap_chart_arrow
      f2_comm_ring f2_comm_ring)
  ≡ @comm_ring_hom_to_zero
      (@comm_ring_localization_target
        f2_split_comm_ring
        f2_split_cosplit_idempotent
        f2_split_cosplit_idempotent_localization);
