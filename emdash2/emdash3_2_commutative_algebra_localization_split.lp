/*
  Split-idempotent localization and a closed non-endpoint affine basic open.

  In every product R x S, e=(1,0) is idempotent.  The fixed-image localization
  at e computes by the idempotent-localization owner, and its affine basic-open
  restriction sends (x,y) to (x,0).  Specializing to F2 x F2 proves e differs
  from both zero and one, giving the first closed genuinely nondegenerate
  localization/basic-open computation in the algebraic-geometry path.

  This module is rule-free.  It carries both object-level ring data and
  structured arrow action through existing owners; it declares no sheaf,
  topology, Spec, or scheme.
*/

require open emdash.emdash3_2_commutative_algebra_product;
require open emdash.emdash3_2_commutative_algebra_f2;
require open emdash.emdash3_2_commutative_algebra_localization_idempotent;
require open emdash.emdash3_2_commutative_algebra_zariski;

// The canonical split idempotent is one in the first factor and zero in the
// second.
symbol comm_ring_product_split_idempotent
  (R S : τ CommRing)
  : τ (@comm_ring_carrier (@comm_ring_product R S))
≔ @Product_pair_grpd
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    (@comm_ring_one R)
    (@comm_ring_zero S);

symbol comm_ring_product_split_idempotent_path
  (R S : τ CommRing)
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_mul
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_product_split_idempotent R S))
      (@comm_ring_product_split_idempotent R S))
≔ @comm_ring_product_pair_path
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    _ _ _ _
    ((@comm_ring_mul_one_law R) (@comm_ring_one R))
    (@comm_ring_mul_zero_right S (@comm_ring_zero S));

// Fixed-image localization selects the first-factor summand computationally.
symbol comm_ring_product_split_localization
  (R S : τ CommRing)
  : τ (@CommRingLocalizationAt
      (@comm_ring_product R S)
      (@comm_ring_product_split_idempotent R S))
≔ @comm_ring_idempotent_image_localization
    (@comm_ring_product R S)
    (@comm_ring_product_split_idempotent R S)
    (@comm_ring_product_split_idempotent_path R S);

// The selected localization is exposed through the existing affine-arrow API.
symbol comm_ring_product_split_basic_open_arrow
  (R S : τ CommRing)
  : τ (Obj (@Into_restr_cat
      (Op_cat CommRing_cat) (@comm_ring_product R S)))
≔ @comm_ring_basic_open_arrow
    (@comm_ring_product R S)
    (@comm_ring_product_split_idempotent R S)
    (@comm_ring_product_split_localization R S);

// Underlying restriction sends a pair (x,y) propositionally to (x,0).
symbol comm_ring_product_split_scale_path
  (R S : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  (y : τ (@comm_ring_carrier S))
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_idempotent_image_element
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_hom_apply
          (@comm_ring_product R S)
          (@comm_ring_idempotent_image
            (@comm_ring_product R S)
            (@comm_ring_product_split_idempotent R S)
            (@comm_ring_product_split_idempotent_path R S))
          (sigma_Snd (@comm_ring_product_split_basic_open_arrow R S))
          (@Product_pair_grpd
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)
            x y)))
      (@Product_pair_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)
        x
        (@comm_ring_zero S)))
≔ @comm_ring_product_pair_path
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    _ _ _ _
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_one R) x)
      (@comm_ring_mul R x (@comm_ring_one R))
      x
      ((@comm_ring_mul_comm_law R) (@comm_ring_one R) x)
      ((@comm_ring_mul_one_law R) x))
    (@comm_ring_mul_zero_left S y);

// F2 x F2 supplies the closed non-endpoint instance.
symbol f2_split_comm_ring
  : τ CommRing
≔ @comm_ring_product f2_comm_ring f2_comm_ring;

symbol f2_split_idempotent
  : τ (@comm_ring_carrier f2_split_comm_ring)
≔ @comm_ring_product_split_idempotent f2_comm_ring f2_comm_ring;

symbol f2_split_idempotent_path
  : τ (@=
      (@comm_ring_carrier f2_split_comm_ring)
      (@comm_ring_mul
        f2_split_comm_ring
        f2_split_idempotent
        f2_split_idempotent)
      f2_split_idempotent)
≔ @comm_ring_product_split_idempotent_path
    f2_comm_ring f2_comm_ring;

// Projecting a hypothetical endpoint path yields a contradictory Boolean path.
symbol f2_split_idempotent_not_zero
  (p : τ (@=
      (@comm_ring_carrier f2_split_comm_ring)
      f2_split_idempotent
      (@comm_ring_zero f2_split_comm_ring)))
  : τ Empty_grpd
≔ @product_path_base
    Bool_grpd Bool_grpd
    f2_split_idempotent
    (@comm_ring_zero f2_split_comm_ring)
    p;

symbol f2_split_idempotent_not_one
  (p : τ (@=
      (@comm_ring_carrier f2_split_comm_ring)
      f2_split_idempotent
      (@comm_ring_one f2_split_comm_ring)))
  : τ Empty_grpd
≔ @const_pathover_path
    Bool_grpd Bool_grpd
    true true false true
    (@product_path_base
      Bool_grpd Bool_grpd
      f2_split_idempotent
      (@comm_ring_one f2_split_comm_ring)
      p)
    (@product_path_fibre
      Bool_grpd Bool_grpd
      f2_split_idempotent
      (@comm_ring_one f2_split_comm_ring)
      p);

symbol f2_split_idempotent_localization
  : τ (@CommRingLocalizationAt
      f2_split_comm_ring f2_split_idempotent)
≔ @comm_ring_product_split_localization f2_comm_ring f2_comm_ring;

symbol f2_split_basic_open_arrow
  : τ (Obj (@Into_restr_cat
      (Op_cat CommRing_cat) f2_split_comm_ring))
≔ @comm_ring_product_split_basic_open_arrow
    f2_comm_ring f2_comm_ring;
