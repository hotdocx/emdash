/*
  Reviewer example: the selected decoder's I tensor_R I interchanger.

  The recursively iterable whole graph retains its internal target-side
  presentation.  The separate standard pointwise square has the literal
  inner-target side, and its filler is definitionally the selected Gray
  interchanger.
*/

require open emdash.emdash3_2_gray_cube_dimension2;

assert ⊢
  gray_cube2_graph_target_side
  : τ (Hom
      GrayWalkingSquare_cat
      gray_square_obj10
      gray_square_obj11);

// The internal whole graph cell retains the internal target-side owner.
assert ⊢
  gray_cube2_interchanger_cell
  : τ (Obj
      (@homdc_square_fibre
        GrayWalkingSquare_cat
        gray_square_obj00
        gray_square_obj01
        gray_square_obj10
        gray_square_obj11
        gray_square_outer_src_arrow
        gray_square_outer_tgt_arrow
        gray_square_inner_src_arrow
        gray_cube2_graph_target_side));

// The standard pointwise cell has the literal four Gray-square sides.
assert ⊢
  gray_cube2_standard_interchanger_cell
  : τ (Obj
      (@homdc_square_fibre
        GrayWalkingSquare_cat
        gray_square_obj00
        gray_square_obj01
        gray_square_obj10
        gray_square_obj11
        gray_square_outer_src_arrow
        gray_square_outer_tgt_arrow
        gray_square_inner_src_arrow
        gray_square_inner_tgt_arrow));

assert ⊢ gray_cube2_standard_interchanger_cell ≡ gray_interchanger;

assert ⊢
  gray_cube2_standard_interchanger_path
  : τ (@=
      (Obj
        (@homdc_square_fibre
          GrayWalkingSquare_cat
          gray_square_obj00
          gray_square_obj01
          gray_square_obj10
          gray_square_obj11
          gray_square_outer_src_arrow
          gray_square_outer_tgt_arrow
          gray_square_inner_src_arrow
          gray_square_inner_tgt_arrow))
      gray_cube2_standard_interchanger_cell
      gray_interchanger);

assert ⊢
  gray_cube2_graph_next_func
  : τ (Functor
      (Hom_cat
        WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
      (Hom_cat
        (@LaxArrow_cat GrayWalkingSquare_cat)
        (@gray_transf_graph_obj
          WalkingArrow_cat GrayWalkingSquare_cat
          gray_square_inner_src_func gray_square_inner_tgt_func
          gray_square_outer_transf walking_arrow_src)
        (@gray_transf_graph_obj
          WalkingArrow_cat GrayWalkingSquare_cat
          gray_square_inner_src_func gray_square_inner_tgt_func
          gray_square_outer_transf walking_arrow_tgt)));
