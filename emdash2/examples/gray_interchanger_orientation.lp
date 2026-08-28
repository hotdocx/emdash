/*
  Reviewer for the typed Gray-interchanger orientation and its
  coordinate-swapped native cubical reading.
*/

require open emdash.emdash3_2_gray_interchanger_orientation;

// catalog-area: Typed Gray orientation and coordinate-swapped cubical reading
// Stable endpoints are compared to visible composites, and the same directed
// cell inhabits the native cubical classifier only after exchanging axes.

// The stable whole-action endpoints have first-class readable comparisons.
assert ⊢
  gray_interchanger_source_readable_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_source
      gray_square_post_composite);

assert ⊢
  gray_interchanger_target_readable_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_target
      gray_square_pre_composite);

// The selected right-Gray cell is visibly v o a ==> b o u.
assert ⊢
  gray_interchanger_readable
  : τ (Hom
      GrayInterchangerCodomain_cat
      gray_square_post_composite
      gray_square_pre_composite);

// Swapping coordinate roles makes exactly that direction a native lax square.
assert ⊢
  gray_interchanger_swapped_square
  : τ (Hom
      (@CubicalArrow_cat GrayWalkingSquare_cat)
      (@cubical_edge
        GrayWalkingSquare_cat
        gray_square_obj00 gray_square_obj10
        gray_square_outer_src_arrow)
      (@cubical_edge
        GrayWalkingSquare_cat
        gray_square_obj01 gray_square_obj11
        gray_square_outer_tgt_arrow));

// Without the coordinate swap the native filler expects the reverse cell.
assertnot ⊢
  @cubical_square
    GrayWalkingSquare_cat
    gray_square_obj00 gray_square_obj10
    gray_square_obj01 gray_square_obj11
    gray_square_inner_src_arrow
    gray_square_inner_tgt_arrow
    gray_square_outer_src_arrow
    gray_square_outer_tgt_arrow
    gray_interchanger_readable
  : τ (Hom
      (@CubicalArrow_cat GrayWalkingSquare_cat)
      (@cubical_edge
        GrayWalkingSquare_cat
        gray_square_obj00 gray_square_obj01
        gray_square_inner_src_arrow)
      (@cubical_edge
        GrayWalkingSquare_cat
        gray_square_obj10 gray_square_obj11
        gray_square_inner_tgt_arrow));
