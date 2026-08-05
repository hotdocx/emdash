/*
  Computational affine Spec facade over commutative rings.

  The conventional big affine slice over Spec(R) is the opposite of the
  existing restriction-oriented category of R-algebras. Its coordinate-ring
  presheaf is the first projection from the opposite Sigma presentation.
  Generic Sigma owners therefore carry both chart arrows and their whole
  structured restriction maps.

  Selected one-element and iterated localizations give basic-open charts.
  The canonical product/iterated-localization comparison maps lift to chart
  arrows in both geometric directions, while coordinate restriction computes
  to the already-proved whole CommRing maps. Their inverse laws remain at the
  localization-overlap owner.

  This rule-free module is a scheme-facing computational precursor. The big
  slice is not a selected small Zariski site, and the module claims neither a
  topology, sheafhood, locally ringed structure, nor a complete scheme.
*/

require open emdash.emdash3_2_commutative_algebra_zariski;
require open emdash.emdash3_2_commutative_algebra_presheaves;
require open emdash.emdash3_2_commutative_algebra_localization_overlap;

// The big affine slice Aff/Spec(R), with conventional geometric direction.
symbol AffineSpecBigSlice_cat
  (R : τ CommRing)
  : Cat
≔ @Slice_cat (Op_cat CommRing_cat) R;

// Coordinate rings form a CommRing-valued presheaf on the big affine slice.
// On its opposite this is the existing Sigma first projection.
symbol affine_spec_coordinate_psh
  (R : τ CommRing)
  : τ (@CommRingPsh (@AffineSpecBigSlice_cat R))
≔ @Sigma_proj1_func
    CommRing_cat
    (@yoneda_psh (Op_cat CommRing_cat) R);

// A structured map R -> S presents the corresponding affine chart over R.
symbol affine_spec_chart
  [R S : τ CommRing]
  (structure_map : τ (@CommRingHom R S))
  : τ (Obj (@AffineSpecBigSlice_cat R))
≔ @Struct_sigma
    (Obj CommRing_cat)
    (λ T : τ (Obj CommRing_cat),
      Obj (@Fibre_cat
        CommRing_cat
        (@yoneda_psh (Op_cat CommRing_cat) R)
        T))
    S structure_map;

// The identity R-algebra is the distinguished whole affine chart.
symbol affine_spec_whole_chart
  (R : τ CommRing)
  : τ (Obj (@AffineSpecBigSlice_cat R))
≔ @affine_spec_chart R R (@comm_ring_hom_id R);

// A chosen localization is its selected basic-open chart D(f).
symbol affine_spec_basic_open_chart
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  : τ (Obj (@AffineSpecBigSlice_cat R))
≔ @comm_ring_basic_open_arrow R f localization;

// Two successive chosen localizations present the iterated basic-open chart.
symbol affine_spec_iterated_basic_open_chart
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (Obj (@AffineSpecBigSlice_cat R))
≔ @affine_spec_chart
    R
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_map R f g iterated);

// A commuting structured triangle R -> S -> T gives the geometric chart
// arrow Spec(T) -> Spec(S). The Sigma owner carries the whole arrow.
symbol affine_spec_chart_arrow
  [R S T : τ CommRing]
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
      target_structure_map))
  : τ (Hom
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R T target_structure_map)
      (@affine_spec_chart R S structure_map))
≔ @sigma_arrow
    CommRing_cat
    (@yoneda_psh (Op_cat CommRing_cat) R)
    S T structure_map target_structure_map map
    (@path_to_hom
      (@Fibre_cat
        CommRing_cat
        (@yoneda_psh (Op_cat CommRing_cat) R)
        T)
      _ _ triangle);

// Convert a pointwise structured-map agreement into the exact opposite-
// precomposition triangle consumed by the affine chart-arrow constructor.
protected symbol affine_spec_chart_triangle_from_pointwise
  [R S T : τ CommRing]
  [structure_map : τ (@CommRingHom R S)]
  [target_structure_map : τ (@CommRingHom R T)]
  (map : τ (@CommRingHom S T))
  (agreement : τ (@CommRingLocalizationAgreement
      R S T structure_map map target_structure_map))
  : τ (@=
      (@CommRingHom R T)
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        R T S map structure_map)
      target_structure_map)
≔ @eq_trans
    (@CommRingHom R T)
    (@hom_precomp_along_fapp0
      (Op_cat CommRing_cat)
      (Op_cat CommRing_cat)
      (@id_func (Op_cat CommRing_cat))
      R T S map structure_map)
    (@comm_ring_hom_comp_pointwise R S T map structure_map)
    target_structure_map
    (@comm_ring_affine_op_precomp_pointwise_path
      R S T map structure_map)
    (@comm_ring_hom_ext
      R T
      (@comm_ring_hom_comp_pointwise R S T map structure_map)
      target_structure_map
      agreement);

// Geometrically, the forward ring comparison gives
// D(f) intersect D(g) -> D(fg).
symbol affine_spec_overlap_forward_chart_arrow
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (Hom
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_iterated_basic_open_chart R f g iterated)
      (@affine_spec_basic_open_chart
        R (@comm_ring_mul R f g) product_localization))
≔ @affine_spec_chart_arrow
    R
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization
      (@comm_ring_iterated_localization_comparison
        R f g iterated product_localization))
    (@affine_spec_chart_triangle_from_pointwise
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization
        (@comm_ring_iterated_localization_comparison
          R f g iterated product_localization))
      (@comm_ring_iterated_localization_comparison_forward_agreement
        R f g iterated product_localization
        (@comm_ring_iterated_localization_comparison
          R f g iterated product_localization)));

// The reverse comparison gives the opposite geometric overlap chart arrow.
symbol affine_spec_overlap_reverse_chart_arrow
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (Hom
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_basic_open_chart
        R (@comm_ring_mul R f g) product_localization)
      (@affine_spec_iterated_basic_open_chart R f g iterated))
≔ @affine_spec_chart_arrow
    R
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization
      (@comm_ring_iterated_localization_comparison
        R f g iterated product_localization))
    (@affine_spec_chart_triangle_from_pointwise
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization
        (@comm_ring_iterated_localization_comparison
          R f g iterated product_localization))
      (@comm_ring_iterated_localization_comparison_reverse_agreement
        R f g iterated product_localization
        (@comm_ring_iterated_localization_comparison
          R f g iterated product_localization)));

// Scheme-facing name for the existing whole coordinate-ring overlap
// equivalence; all maps and cancellation paths stay at their algebra owner.
symbol affine_spec_overlap_coordinate_omega_equiv
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@OmegaEquiv
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated))
≔ @comm_ring_iterated_localization_comparison_omega_equiv
    R f g iterated product_localization
    (@comm_ring_iterated_localization_comparison
      R f g iterated product_localization);
