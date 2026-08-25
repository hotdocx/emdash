/*
  Emdash v3.2: selected dimension-two reading of the Gray-cube decoder.

  For the identity realization of I tensor_R I, the decoder's curry step is
  exactly the established coevaluation walking square.  Its transformation
  graph therefore exposes the same internal-action interchanger, with native
  coordinate-swapped direction

    target_side o outer_source  ==>  outer_target o inner_source.

  The target side deliberately remains the total-base-change/internal-action
  projection.  `gray_interchanger_readable` additionally reframes that side to
  the separately named inner-target arrow, so no direct equality between those
  differently presented cells is asserted.  The whole graph action remains
  available for the next dimension.
*/

require open emdash.emdash3_2_gray_cube_decoder;

symbol gray_cube2_graph_target_side
  : τ (Hom
      GrayWalkingSquare_cat
      gray_square_obj10
      gray_square_obj11)
≔ @gray_transf_graph_target_side
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    gray_square_outer_transf
    walking_arrow_src walking_arrow_tgt
    walking_arrow_generator;

symbol gray_cube2_interchanger_cell
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
        gray_cube2_graph_target_side))
≔ @gray_transf_graph_cell
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    gray_square_outer_transf
    walking_arrow_src walking_arrow_tgt
    walking_arrow_generator;

symbol gray_cube2_graph_next_func
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
          gray_square_outer_transf walking_arrow_tgt)))
≔ @gray_transf_graph_next_func
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    gray_square_outer_transf
    walking_arrow_src walking_arrow_tgt;
