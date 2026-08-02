/*
  Reviewer-facing computational affine Spec slice.

  A ring map R -> S is an affine chart over R, and coordinate rings form an
  actual CommRing-valued presheaf on the conventional big affine slice. The
  product/iterated-localization overlap is represented by internal chart
  arrows in both directions; coordinate restriction computes to the existing
  whole structured comparison maps.

  This is an executable affine-chart precursor, not yet a selected small
  Zariski site, a sheaf, a locally ringed space, or a complete scheme.
*/

require open emdash.emdash3_2_commutative_algebra_affine_spec;
require open emdash.emdash3_2_commutative_algebra_localization_split;

// Coordinate rings are a genuine presheaf on the conventional big slice.
assert (R : τ CommRing) ⊢
  @affine_spec_coordinate_psh R
  : τ (@CommRingPsh (@AffineSpecBigSlice_cat R));

// The whole chart has coordinate ring R.
assert (R : τ CommRing) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_whole_chart R)
  ≡ R;

// The selected basic-open chart D(f) has coordinate ring R[1/f].
assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_basic_open_chart R f localization)
  ≡ @comm_ring_localization_target R f localization;

// For every structured triangle R -> S -> T, geometric restriction along
// Spec(T) -> Spec(S) computes to the supplied whole structured map S -> T.
assert [R S T : τ CommRing]
  [structure_map : τ (@CommRingHom R S)]
  [target_structure_map : τ (@CommRingHom R T)]
  (map : τ (@CommRingHom S T))
  (triangle : τ (@=
      (@CommRingHom R T)
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        R T S map structure_map)
      target_structure_map)) ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_chart R T target_structure_map)
    (@affine_spec_chart R S structure_map)
    (@affine_spec_chart_arrow
      R S T structure_map target_structure_map map triangle)
  ≡ map;

// The forward overlap chart restriction is the whole comparison
// R[1/(f*g)] -> R[1/f][1/g].
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_iterated_basic_open_chart R f g iterated)
    (@affine_spec_basic_open_chart
      R (@comm_ring_mul R f g) product_localization)
    (@affine_spec_overlap_forward_chart_arrow
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization
      (@comm_ring_iterated_localization_comparison
        R f g iterated product_localization);

// The reverse geometric arrow computes to the staged reverse ring map.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@affine_spec_basic_open_chart
      R (@comm_ring_mul R f g) product_localization)
    (@affine_spec_iterated_basic_open_chart R f g iterated)
    (@affine_spec_overlap_reverse_chart_arrow
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization
      (@comm_ring_iterated_localization_comparison
        R f g iterated product_localization);

// Their coordinate-ring equivalence retains the canonical forward map and
// the already-derived whole cancellation paths.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @affine_spec_overlap_coordinate_omega_equiv
    R f g iterated product_localization
  : τ (@OmegaEquiv
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated));

assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @omega_equiv_to
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@affine_spec_overlap_coordinate_omega_equiv
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization
      (@comm_ring_iterated_localization_comparison
        R f g iterated product_localization);

// The closed non-endpoint split idempotent supplies an actual selected
// basic-open chart in this facade.
assert ⊢
  @affine_spec_basic_open_chart
    f2_split_comm_ring
    f2_split_idempotent
    f2_split_idempotent_localization
  ≡ f2_split_basic_open_arrow;

assert ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat f2_split_comm_ring)
    (@affine_spec_coordinate_psh f2_split_comm_ring)
    (@affine_spec_basic_open_chart
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_localization)
  ≡ @comm_ring_localization_target
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_localization;
