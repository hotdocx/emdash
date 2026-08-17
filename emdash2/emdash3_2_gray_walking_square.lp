/*
  Emdash v3.2: the walking square inside the selected Gray right tensor.

  The four vertices and both coordinate directions are derived from the
  right coevaluation of I tensor I.  The inner direction composes the whole
  walking-generator owner with each inner functor's hom action.  The outer
  direction is one whole transformation obtained by applying coevaluation to
  the outer generator, observed through the existing whole component
  evaluators.  No tensor vertex, edge, rule, or unifier is postulated here.

  This module supplies the boundary consumed by the subsequent interchanger
  projection.  It does not yet identify the selected profile's lax/oplax
  orientation or claim the Cartesian, mirror-closed, or monoidal structure.
*/

require open emdash.emdash3_2_gray_right_closure;
require open emdash.emdash3_2_walking_arrow;

// The selected walking square is the opaque right tensor I tensor I.
symbol GrayWalkingSquare_cat
  : Cat
≔ @GrayTensor_R WalkingArrow_cat WalkingArrow_cat;

// Evaluating coevaluation at the outer endpoints yields strict inner codes.
symbol gray_square_inner_src_data
  : τ (@StrictFunctorData WalkingArrow_cat GrayWalkingSquare_cat)
≔ @fapp0
    WalkingArrow_cat
    (@GrayHom_oplax WalkingArrow_cat GrayWalkingSquare_cat)
    (@gray_coevaluation_R_func WalkingArrow_cat WalkingArrow_cat)
    walking_arrow_src;

symbol gray_square_inner_tgt_data
  : τ (@StrictFunctorData WalkingArrow_cat GrayWalkingSquare_cat)
≔ @fapp0
    WalkingArrow_cat
    (@GrayHom_oplax WalkingArrow_cat GrayWalkingSquare_cat)
    (@gray_coevaluation_R_func WalkingArrow_cat WalkingArrow_cat)
    walking_arrow_tgt;

// Decode the two inner functors while retaining their strict profile heads.
symbol gray_square_inner_src_func
  : τ (Functor WalkingArrow_cat GrayWalkingSquare_cat)
≔ @strict_functor_carrier
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_data;

symbol gray_square_inner_tgt_func
  : τ (Functor WalkingArrow_cat GrayWalkingSquare_cat)
≔ @strict_functor_carrier
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_tgt_data;

// The four vertices are the two inner functors at the two inner endpoints.
symbol gray_square_obj00
  : τ (Obj GrayWalkingSquare_cat)
≔ @fapp0
    WalkingArrow_cat GrayWalkingSquare_cat
    gray_square_inner_src_func walking_arrow_src;

symbol gray_square_obj01
  : τ (Obj GrayWalkingSquare_cat)
≔ @fapp0
    WalkingArrow_cat GrayWalkingSquare_cat
    gray_square_inner_src_func walking_arrow_tgt;

symbol gray_square_obj10
  : τ (Obj GrayWalkingSquare_cat)
≔ @fapp0
    WalkingArrow_cat GrayWalkingSquare_cat
    gray_square_inner_tgt_func walking_arrow_src;

symbol gray_square_obj11
  : τ (Obj GrayWalkingSquare_cat)
≔ @fapp0
    WalkingArrow_cat GrayWalkingSquare_cat
    gray_square_inner_tgt_func walking_arrow_tgt;

/*
  Whole inner-coordinate owners.  Each is the composite of the retained
  walking-generator functor 1 -> Hom_I(0,1) with the corresponding strict
  inner functor's whole hom action.
*/
symbol gray_square_inner_src_generator_func
  : τ (Functor
      Terminal_cat
      (Hom_cat
        GrayWalkingSquare_cat
        gray_square_obj00
        gray_square_obj01))
≔ @comp_cat_fapp0
    Terminal_cat
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    (Hom_cat
      GrayWalkingSquare_cat
      gray_square_obj00
      gray_square_obj01)
    (@fapp1_func
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      walking_arrow_src
      walking_arrow_tgt)
    walking_arrow_generator_func;

symbol gray_square_inner_tgt_generator_func
  : τ (Functor
      Terminal_cat
      (Hom_cat
        GrayWalkingSquare_cat
        gray_square_obj10
        gray_square_obj11))
≔ @comp_cat_fapp0
    Terminal_cat
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    (Hom_cat
      GrayWalkingSquare_cat
      gray_square_obj10
      gray_square_obj11)
    (@fapp1_func
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_tgt_func
      walking_arrow_src
      walking_arrow_tgt)
    walking_arrow_generator_func;

// Inner-coordinate arrows are the terminal components of those whole owners.
symbol gray_square_inner_src_arrow
  : τ (Hom
      GrayWalkingSquare_cat
      gray_square_obj00
      gray_square_obj01)
≔ @fapp0
    Terminal_cat
    (Hom_cat
      GrayWalkingSquare_cat
      gray_square_obj00
      gray_square_obj01)
    gray_square_inner_src_generator_func
    Terminal_obj;

symbol gray_square_inner_tgt_arrow
  : τ (Hom
      GrayWalkingSquare_cat
      gray_square_obj10
      gray_square_obj11)
≔ @fapp0
    Terminal_cat
    (Hom_cat
      GrayWalkingSquare_cat
      gray_square_obj10
      gray_square_obj11)
    gray_square_inner_tgt_generator_func
    Terminal_obj;

/*
  The outer generator acts through coevaluation as one whole transformation
  between the two inner functors.  Its endpoint evaluators remain whole
  functors on the transformation category.
*/
symbol gray_square_outer_transf
  : τ (@Transf
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func)
≔ @fapp1_fapp0
    WalkingArrow_cat
    (@GrayHom_oplax WalkingArrow_cat GrayWalkingSquare_cat)
    (@gray_coevaluation_R_func WalkingArrow_cat WalkingArrow_cat)
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator;

// Whole endpoint-component evaluators for the outer coordinate direction.
symbol gray_square_outer_src_eval_func
  : τ (Functor
      (@Transf_cat
        WalkingArrow_cat
        GrayWalkingSquare_cat
        gray_square_inner_src_func
        gray_square_inner_tgt_func)
      (Hom_cat
        GrayWalkingSquare_cat
        gray_square_obj00
        gray_square_obj10))
≔ @tapp0_func
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    walking_arrow_src;

symbol gray_square_outer_tgt_eval_func
  : τ (Functor
      (@Transf_cat
        WalkingArrow_cat
        GrayWalkingSquare_cat
        gray_square_inner_src_func
        gray_square_inner_tgt_func)
      (Hom_cat
        GrayWalkingSquare_cat
        gray_square_obj01
        gray_square_obj11))
≔ @tapp0_func
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    walking_arrow_tgt;

// Outer-coordinate arrows are the two components of the same transformation.
symbol gray_square_outer_src_arrow
  : τ (Hom
      GrayWalkingSquare_cat
      gray_square_obj00
      gray_square_obj10)
≔ @fapp0
    (@Transf_cat
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func)
    (Hom_cat
      GrayWalkingSquare_cat
      gray_square_obj00
      gray_square_obj10)
    gray_square_outer_src_eval_func
    gray_square_outer_transf;

symbol gray_square_outer_tgt_arrow
  : τ (Hom
      GrayWalkingSquare_cat
      gray_square_obj01
      gray_square_obj11)
≔ @fapp0
    (@Transf_cat
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func)
    (Hom_cat
      GrayWalkingSquare_cat
      gray_square_obj01
      gray_square_obj11)
    gray_square_outer_tgt_eval_func
    gray_square_outer_transf;
