/*
  A computational two-chart affine atlas from complementary idempotents.

  In every product ring R x S, the idempotents e=(1,0) and e'=(0,1) are
  complementary and orthogonal.  Their fixed-image localizations form an
  explicitly selected binary Zariski cover.  Since e*e'=0, their affine
  basic-open overlap presentation is the existing computing zero localization.

  The two overlap maps are actual arrows of the affine big slice, and the
  coordinate presheaf restricts along them to the unique whole structured
  maps from the chart rings to the zero ring.  This gives a closed atlas/glue
  presentation for Spec(R x S), specialized below to F2 x F2, while retaining
  all object and arrow action at existing CommRing, Sigma, and functor owners.

  This rule-free module does not construct a small site, sheaf, locally ringed
  space, colimit/universal gluing theorem, or general scheme record.
*/

require open emdash.emdash3_2_commutative_algebra_affine_spec;
require open emdash.emdash3_2_commutative_algebra_localization_split;
require open emdash.emdash3_2_commutative_algebra_localization_zero;

// The complementary split idempotent is zero in the first factor and one in
// the second.
symbol comm_ring_product_cosplit_idempotent
  (R S : τ CommRing)
  : τ (@comm_ring_carrier (@comm_ring_product R S))
≔ @Product_pair_grpd
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    (@comm_ring_zero R)
    (@comm_ring_one S);

symbol comm_ring_product_cosplit_idempotent_path
  (R S : τ CommRing)
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_product_cosplit_idempotent R S)
        (@comm_ring_product_cosplit_idempotent R S))
      (@comm_ring_product_cosplit_idempotent R S))
≔ @comm_ring_product_pair_path
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    _ _ _ _
    (@comm_ring_mul_zero_right R (@comm_ring_zero R))
    ((@comm_ring_mul_one_law S) (@comm_ring_one S));

// Fixed-image localization at (0,1) selects the second summand.
symbol comm_ring_product_cosplit_localization
  (R S : τ CommRing)
  : τ (@CommRingLocalizationAt
      (@comm_ring_product R S)
      (@comm_ring_product_cosplit_idempotent R S))
≔ @comm_ring_idempotent_image_localization
    (@comm_ring_product R S)
    (@comm_ring_product_cosplit_idempotent R S)
    (@comm_ring_product_cosplit_idempotent_path R S);

// Componentwise, (1,0)+(0,1)=(1,1).
symbol comm_ring_product_split_cosplit_sum_path
  (R S : τ CommRing)
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_add
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_cosplit_idempotent R S))
      (@comm_ring_one (@comm_ring_product R S)))
≔ @comm_ring_product_pair_path
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    _ _ _ _
    ((@comm_ring_add_zero_law R) (@comm_ring_one R))
    (@eq_trans
      (@comm_ring_carrier S)
      (@comm_ring_add S (@comm_ring_zero S) (@comm_ring_one S))
      (@comm_ring_add S (@comm_ring_one S) (@comm_ring_zero S))
      (@comm_ring_one S)
      ((@comm_ring_add_comm_law S)
        (@comm_ring_zero S) (@comm_ring_one S))
      ((@comm_ring_add_zero_law S) (@comm_ring_one S)));

// Unit coefficients witness that the two idempotents generate the unit ideal.
symbol comm_ring_product_split_cosplit_cover_law
  (R S : τ CommRing)
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_add
        (@comm_ring_product R S)
        (@comm_ring_mul
          (@comm_ring_product R S)
          (@comm_ring_one (@comm_ring_product R S))
          (@comm_ring_product_split_idempotent R S))
        (@comm_ring_mul
          (@comm_ring_product R S)
          (@comm_ring_one (@comm_ring_product R S))
          (@comm_ring_product_cosplit_idempotent R S)))
      (@comm_ring_one (@comm_ring_product R S)))
≔ @eq_trans
    (@comm_ring_carrier (@comm_ring_product R S))
    (@comm_ring_add
      (@comm_ring_product R S)
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_one (@comm_ring_product R S))
        (@comm_ring_product_split_idempotent R S))
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_one (@comm_ring_product R S))
        (@comm_ring_product_cosplit_idempotent R S)))
    (@comm_ring_add
      (@comm_ring_product R S)
      (@comm_ring_product_split_idempotent R S)
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_one (@comm_ring_product R S))
        (@comm_ring_product_cosplit_idempotent R S)))
    (@comm_ring_one (@comm_ring_product R S))
    (@eq_ap
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_carrier (@comm_ring_product R S))
      (λ x : τ (@comm_ring_carrier (@comm_ring_product R S)),
        @comm_ring_add
          (@comm_ring_product R S)
          x
          (@comm_ring_mul
            (@comm_ring_product R S)
            (@comm_ring_one (@comm_ring_product R S))
            (@comm_ring_product_cosplit_idempotent R S)))
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_one (@comm_ring_product R S))
        (@comm_ring_product_split_idempotent R S))
      (@comm_ring_product_split_idempotent R S)
      (@comm_ring_one_mul_law
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)))
    (@eq_trans
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_add
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_mul
          (@comm_ring_product R S)
          (@comm_ring_one (@comm_ring_product R S))
          (@comm_ring_product_cosplit_idempotent R S)))
      (@comm_ring_add
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_cosplit_idempotent R S))
      (@comm_ring_one (@comm_ring_product R S))
      (@eq_ap
        (@comm_ring_carrier (@comm_ring_product R S))
        (@comm_ring_carrier (@comm_ring_product R S))
        (λ x : τ (@comm_ring_carrier (@comm_ring_product R S)),
          @comm_ring_add
            (@comm_ring_product R S)
            (@comm_ring_product_split_idempotent R S)
            x)
        (@comm_ring_mul
          (@comm_ring_product R S)
          (@comm_ring_one (@comm_ring_product R S))
          (@comm_ring_product_cosplit_idempotent R S))
        (@comm_ring_product_cosplit_idempotent R S)
        (@comm_ring_one_mul_law
          (@comm_ring_product R S)
          (@comm_ring_product_cosplit_idempotent R S)))
      (@comm_ring_product_split_cosplit_sum_path R S));

// The retained algebraic presentation has the two complementary generators.
symbol comm_ring_product_split_cosplit_zariski_cover
  (R S : τ CommRing)
  : τ (@CommRingZariskiCoverPresentation (@comm_ring_product R S))
≔ @comm_ring_binary_zariski_cover
    (@comm_ring_product R S)
    (@comm_ring_product_split_idempotent R S)
    (@comm_ring_product_cosplit_idempotent R S)
    (@comm_ring_one (@comm_ring_product R S))
    (@comm_ring_one (@comm_ring_product R S))
    (@comm_ring_product_split_cosplit_cover_law R S);

// Both fixed-image localization packages remain explicitly selected.
symbol comm_ring_product_split_cosplit_localizations
  (R S : τ CommRing)
  : τ (@CommRingLocalizationFamily
      (@comm_ring_product R S)
      (succ (succ zero))
      (@finite_family_pair
        (@comm_ring_carrier (@comm_ring_product R S))
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_cosplit_idempotent R S)))
≔ @comm_ring_localization_family_cons
    (@comm_ring_product R S)
    (succ zero)
    (@comm_ring_product_split_idempotent R S)
    (@finite_family_singleton
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_product_cosplit_idempotent R S))
    (@comm_ring_product_split_localization R S)
    (@comm_ring_localization_family_singleton
      (@comm_ring_product R S)
      (@comm_ring_product_cosplit_idempotent R S)
      (@comm_ring_product_cosplit_localization R S));

// This existing cover-family package is the atlas's source of truth.
symbol comm_ring_product_split_cosplit_zariski_cover_family
  (R S : τ CommRing)
  : τ (@CommRingZariskiCoverFamily (@comm_ring_product R S))
≔ @comm_ring_zariski_cover_family_intro
    (@comm_ring_product R S)
    (@comm_ring_product_split_cosplit_zariski_cover R S)
    (@comm_ring_product_split_cosplit_localizations R S);

// Orthogonality identifies the selected product-generator overlap with D(0).
symbol comm_ring_product_split_cosplit_product_zero_path
  (R S : τ CommRing)
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_cosplit_idempotent R S))
      (@comm_ring_zero (@comm_ring_product R S)))
≔ @comm_ring_product_pair_path
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    _ _ _ _
    (@comm_ring_mul_zero_right R (@comm_ring_one R))
    (@comm_ring_mul_zero_left S (@comm_ring_one S));

// The two selected affine charts and their computational empty overlap.
symbol affine_spec_product_split_chart
  (R S : τ CommRing)
  : τ (Obj (@AffineSpecBigSlice_cat (@comm_ring_product R S)))
≔ @affine_spec_basic_open_chart
    (@comm_ring_product R S)
    (@comm_ring_product_split_idempotent R S)
    (@comm_ring_product_split_localization R S);

symbol affine_spec_product_cosplit_chart
  (R S : τ CommRing)
  : τ (Obj (@AffineSpecBigSlice_cat (@comm_ring_product R S)))
≔ @affine_spec_basic_open_chart
    (@comm_ring_product R S)
    (@comm_ring_product_cosplit_idempotent R S)
    (@comm_ring_product_cosplit_localization R S);

symbol affine_spec_product_split_cosplit_overlap_chart
  (R S : τ CommRing)
  : τ (Obj (@AffineSpecBigSlice_cat (@comm_ring_product R S)))
≔ @affine_spec_basic_open_chart
    (@comm_ring_product R S)
    (@comm_ring_zero (@comm_ring_product R S))
    (@comm_ring_zero_localization (@comm_ring_product R S));

// Any structured map followed by the point map to zero agrees with the point
// map from its source, first pointwise and then in the affine Sigma fibre.
protected symbol comm_ring_hom_to_zero_pointwise_path
  [R S : τ CommRing]
  (structure_map : τ (@CommRingHom R S))
  : τ (@=
      (@CommRingHom R zero_comm_ring)
      (@comm_ring_hom_comp_pointwise
        R S zero_comm_ring
        (@comm_ring_hom_to_zero S)
        structure_map)
      (@comm_ring_hom_to_zero R))
≔ @comm_ring_hom_ext
    R zero_comm_ring
    (@comm_ring_hom_comp_pointwise
      R S zero_comm_ring
      (@comm_ring_hom_to_zero S)
      structure_map)
    (@comm_ring_hom_to_zero R)
    (λ _ : τ (@comm_ring_carrier R), @eq_refl Unit_grpd tt);

protected symbol comm_ring_hom_to_zero_affine_triangle
  [R S : τ CommRing]
  (structure_map : τ (@CommRingHom R S))
  : τ (@=
      (@CommRingHom R zero_comm_ring)
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        R zero_comm_ring S
        (@comm_ring_hom_to_zero S)
        structure_map)
      (@comm_ring_hom_to_zero R))
≔ @eq_trans
    (@CommRingHom R zero_comm_ring)
    (@hom_precomp_along_fapp0
      (Op_cat CommRing_cat)
      (Op_cat CommRing_cat)
      (@id_func (Op_cat CommRing_cat))
      R zero_comm_ring S
      (@comm_ring_hom_to_zero S)
      structure_map)
    (@comm_ring_hom_comp_pointwise
      R S zero_comm_ring
      (@comm_ring_hom_to_zero S)
      structure_map)
    (@comm_ring_hom_to_zero R)
    (@comm_ring_affine_op_precomp_pointwise_path
      R S zero_comm_ring
      (@comm_ring_hom_to_zero S)
      structure_map)
    (@comm_ring_hom_to_zero_pointwise_path R S structure_map);

// The empty overlap maps geometrically into the first chart.
symbol affine_spec_product_split_overlap_chart_arrow
  (R S : τ CommRing)
  : τ (Hom
      (@AffineSpecBigSlice_cat (@comm_ring_product R S))
      (@affine_spec_product_split_cosplit_overlap_chart R S)
      (@affine_spec_product_split_chart R S))
≔ @affine_spec_chart_arrow
    (@comm_ring_product R S)
    (@comm_ring_localization_target
      (@comm_ring_product R S)
      (@comm_ring_product_split_idempotent R S)
      (@comm_ring_product_split_localization R S))
    zero_comm_ring
    (@comm_ring_localization_map
      (@comm_ring_product R S)
      (@comm_ring_product_split_idempotent R S)
      (@comm_ring_product_split_localization R S))
    (@comm_ring_hom_to_zero (@comm_ring_product R S))
    (@comm_ring_hom_to_zero
      (@comm_ring_localization_target
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_split_localization R S)))
    (@comm_ring_hom_to_zero_affine_triangle
      (@comm_ring_product R S)
      (@comm_ring_localization_target
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_split_localization R S))
      (@comm_ring_localization_map
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_split_localization R S)));

// The empty overlap maps geometrically into the complementary chart.
symbol affine_spec_product_cosplit_overlap_chart_arrow
  (R S : τ CommRing)
  : τ (Hom
      (@AffineSpecBigSlice_cat (@comm_ring_product R S))
      (@affine_spec_product_split_cosplit_overlap_chart R S)
      (@affine_spec_product_cosplit_chart R S))
≔ @affine_spec_chart_arrow
    (@comm_ring_product R S)
    (@comm_ring_localization_target
      (@comm_ring_product R S)
      (@comm_ring_product_cosplit_idempotent R S)
      (@comm_ring_product_cosplit_localization R S))
    zero_comm_ring
    (@comm_ring_localization_map
      (@comm_ring_product R S)
      (@comm_ring_product_cosplit_idempotent R S)
      (@comm_ring_product_cosplit_localization R S))
    (@comm_ring_hom_to_zero (@comm_ring_product R S))
    (@comm_ring_hom_to_zero
      (@comm_ring_localization_target
        (@comm_ring_product R S)
        (@comm_ring_product_cosplit_idempotent R S)
        (@comm_ring_product_cosplit_localization R S)))
    (@comm_ring_hom_to_zero_affine_triangle
      (@comm_ring_product R S)
      (@comm_ring_localization_target
        (@comm_ring_product R S)
        (@comm_ring_product_cosplit_idempotent R S)
        (@comm_ring_product_cosplit_localization R S))
      (@comm_ring_localization_map
        (@comm_ring_product R S)
        (@comm_ring_product_cosplit_idempotent R S)
        (@comm_ring_product_cosplit_localization R S)));

// Closed F2 x F2 aliases for the first concrete two-chart atlas.
symbol f2_split_cosplit_idempotent
  : τ (@comm_ring_carrier f2_split_comm_ring)
≔ @comm_ring_product_cosplit_idempotent
    f2_comm_ring f2_comm_ring;

symbol f2_split_cosplit_idempotent_localization
  : τ (@CommRingLocalizationAt
      f2_split_comm_ring f2_split_cosplit_idempotent)
≔ @comm_ring_product_cosplit_localization
    f2_comm_ring f2_comm_ring;

symbol f2_split_cosplit_zariski_cover_family
  : τ (@CommRingZariskiCoverFamily f2_split_comm_ring)
≔ @comm_ring_product_split_cosplit_zariski_cover_family
    f2_comm_ring f2_comm_ring;

symbol f2_split_cosplit_overlap_chart
  : τ (Obj (@AffineSpecBigSlice_cat f2_split_comm_ring))
≔ @affine_spec_product_split_cosplit_overlap_chart
    f2_comm_ring f2_comm_ring;
