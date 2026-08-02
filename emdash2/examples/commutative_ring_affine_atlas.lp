/*
  Reviewer-facing complementary-idempotent affine atlas.

  For every product ring R x S, the selected basic opens at (1,0) and (0,1)
  form an explicit binary Zariski-cover presentation.  Their overlap is the
  computing zero localization, and the coordinate presheaf restricts along
  the two internal overlap arrows by whole structured maps to the zero ring.

  The closed F2 x F2 instance is the first non-endpoint affine atlas/glue
  presentation.  This reviewer does not claim a universal gluing theorem,
  sheafhood, a locally ringed space, or a general scheme record.
*/

require open emdash.emdash3_2_commutative_algebra_affine_atlas;

// The existing presentation/localization package is the source of the two
// selected charts; no parallel chart-family record is introduced.
assert (R S : τ CommRing) ⊢
  @comm_ring_product_split_cosplit_zariski_cover_family R S
  : τ (@CommRingZariskiCoverFamily (@comm_ring_product R S));

assert (R S : τ CommRing) ⊢
  @comm_ring_zariski_cover_family_length
    (@comm_ring_product R S)
    (@comm_ring_product_split_cosplit_zariski_cover_family R S)
  ≡ succ (succ zero);

assert (R S : τ CommRing) ⊢
  @finite_family_head
    (@comm_ring_carrier (@comm_ring_product R S))
    (succ zero)
    (@comm_ring_zariski_cover_family_generators
      (@comm_ring_product R S)
      (@comm_ring_product_split_cosplit_zariski_cover_family R S))
  ≡ @comm_ring_product_split_idempotent R S;

assert (R S : τ CommRing) ⊢
  @comm_ring_localization_family_head
    (@comm_ring_product R S)
    (succ zero)
    (@comm_ring_zariski_cover_family_generators
      (@comm_ring_product R S)
      (@comm_ring_product_split_cosplit_zariski_cover_family R S))
    (@comm_ring_zariski_cover_family_localizations
      (@comm_ring_product R S)
      (@comm_ring_product_split_cosplit_zariski_cover_family R S))
  ≡ @comm_ring_product_split_localization R S;

// The complementary generators are orthogonal, so their overlap is D(0).
assert (R S : τ CommRing) ⊢
  @comm_ring_product_split_cosplit_product_zero_path R S
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_cosplit_idempotent R S))
      (@comm_ring_zero (@comm_ring_product R S)));

// Both chart values are the selected fixed-image localization rings.
assert (R S : τ CommRing) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat (@comm_ring_product R S))
    (@affine_spec_coordinate_psh (@comm_ring_product R S))
    (@affine_spec_product_split_chart R S)
  ≡ @comm_ring_localization_target
      (@comm_ring_product R S)
      (@comm_ring_product_split_idempotent R S)
      (@comm_ring_product_split_localization R S);

assert (R S : τ CommRing) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat (@comm_ring_product R S))
    (@affine_spec_coordinate_psh (@comm_ring_product R S))
    (@affine_spec_product_cosplit_chart R S)
  ≡ @comm_ring_localization_target
      (@comm_ring_product R S)
      (@comm_ring_product_cosplit_idempotent R S)
      (@comm_ring_product_cosplit_localization R S);

// The overlap value and both restriction maps compute at existing generic
// functor/Sigma and structured-ring owners.
assert (R S : τ CommRing) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat (@comm_ring_product R S))
    (@affine_spec_coordinate_psh (@comm_ring_product R S))
    (@affine_spec_product_split_cosplit_overlap_chart R S)
  ≡ zero_comm_ring;

assert (R S : τ CommRing) ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat (@comm_ring_product R S))
    (@affine_spec_coordinate_psh (@comm_ring_product R S))
    (@affine_spec_product_split_cosplit_overlap_chart R S)
    (@affine_spec_product_split_chart R S)
    (@affine_spec_product_split_overlap_chart_arrow R S)
  ≡ @comm_ring_hom_to_zero
      (@comm_ring_localization_target
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_split_localization R S));

assert (R S : τ CommRing) ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat (@comm_ring_product R S))
    (@affine_spec_coordinate_psh (@comm_ring_product R S))
    (@affine_spec_product_split_cosplit_overlap_chart R S)
    (@affine_spec_product_cosplit_chart R S)
    (@affine_spec_product_cosplit_overlap_chart_arrow R S)
  ≡ @comm_ring_hom_to_zero
      (@comm_ring_localization_target
        (@comm_ring_product R S)
        (@comm_ring_product_cosplit_idempotent R S)
        (@comm_ring_product_cosplit_localization R S));

// In F2 x F2 the generator product reduces literally to zero, making this a
// closed, non-endpoint two-chart affine example with computationally empty
// overlap.
assert ⊢
  @comm_ring_mul
    f2_split_comm_ring
    f2_split_idempotent
    f2_split_cosplit_idempotent
  ≡ @comm_ring_zero f2_split_comm_ring;

assert ⊢
  f2_split_cosplit_zariski_cover_family
  : τ (@CommRingZariskiCoverFamily f2_split_comm_ring);

assert ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    f2_split_cosplit_overlap_chart
  ≡ zero_comm_ring;
