/*
  Emdash v3.2: the directed interchanger of the profiled Gray walking square.

  The two readable composites record the boundary of I tensor I.  The actual
  computational owner is the existing whole post/left laxity transformation
  for the coevaluation-generated outer transformation and the retained inner
  generator.  Its identity component is the interchanger, and its whole
  tapp1_func action remains available one dimension higher.

  No independent square cell, endpoint rewrite, or unification rule is added.
  The stable transport owners remain the formal component endpoints; the raw
  composites are their readable presentations under the prototype's tracked
  historical strict endpoint cuts.  The computed direction

      G[g] o epsilon[-]  ==>  epsilon[g o -]

  is the project's standard lax orientation.
*/

require open emdash.emdash3_2_gray_walking_square;

// The two readable directed composites around the walking square.
symbol gray_square_post_composite
  : τ (Hom GrayWalkingSquare_cat gray_square_obj00 gray_square_obj11)
≔ @comp_fapp0
    GrayWalkingSquare_cat
    gray_square_obj00
    gray_square_obj10
    gray_square_obj11
    gray_square_inner_tgt_arrow
    gray_square_outer_src_arrow;

symbol gray_square_pre_composite
  : τ (Hom GrayWalkingSquare_cat gray_square_obj00 gray_square_obj11)
≔ @comp_fapp0
    GrayWalkingSquare_cat
    gray_square_obj00
    gray_square_obj01
    gray_square_obj11
    gray_square_outer_tgt_arrow
    gray_square_inner_src_arrow;

// Domain and codomain of the whole post/left laxity transformation.
symbol GrayInterchangerDomain_cat
  : Cat
≔ @Hom_cat
    WalkingArrow_cat
    walking_arrow_src
    walking_arrow_src;

symbol GrayInterchangerCodomain_cat
  : Cat
≔ @Hom_cat
    GrayWalkingSquare_cat
    gray_square_obj00
    gray_square_obj11;

// Stable whole boundary functors supplied by the internal-action calculus.
symbol gray_interchanger_lhs_func
  : τ (Functor GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)
≔ @functord_transport_lhs_func
    WalkingArrow_cat
    (@hom_
      WalkingArrow_cat
      WalkingArrow_cat
      (@id_func WalkingArrow_cat)
      walking_arrow_src)
    (@hom_
      GrayWalkingSquare_cat
      WalkingArrow_cat
      gray_square_inner_tgt_func
      gray_square_obj00)
    (@tapp1_at_transf
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      walking_arrow_src
      gray_square_outer_transf)
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator;

symbol gray_interchanger_rhs_func
  : τ (Functor GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)
≔ @functord_transport_rhs_func
    WalkingArrow_cat
    (@hom_
      WalkingArrow_cat
      WalkingArrow_cat
      (@id_func WalkingArrow_cat)
      walking_arrow_src)
    (@hom_
      GrayWalkingSquare_cat
      WalkingArrow_cat
      gray_square_inner_tgt_func
      gray_square_obj00)
    (@tapp1_at_transf
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      walking_arrow_src
      gray_square_outer_transf)
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator;

// Whole internal-action owner; the square cell is not postulated separately.
symbol gray_interchanger_transf
  : τ (Transf gray_interchanger_lhs_func gray_interchanger_rhs_func)
≔ @tapp1_post_laxity_transf
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    gray_square_outer_transf
    walking_arrow_src
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator;

symbol gray_interchanger_base_identity
  : τ (Obj GrayInterchangerDomain_cat)
≔ @id WalkingArrow_cat walking_arrow_src;

// Stable source and target observations of the whole laxity owner.
symbol gray_interchanger_source
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @fapp0
    GrayInterchangerDomain_cat
    GrayInterchangerCodomain_cat
    gray_interchanger_lhs_func
    gray_interchanger_base_identity;

symbol gray_interchanger_target
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @fapp0
    GrayInterchangerDomain_cat
    GrayInterchangerCodomain_cat
    gray_interchanger_rhs_func
    gray_interchanger_base_identity;

// The directed interchanger is the identity component of the whole owner.
symbol gray_interchanger
  : τ (Hom
      GrayInterchangerCodomain_cat
      gray_interchanger_source
      gray_interchanger_target)
≔ @tapp0_fapp0
    GrayInterchangerDomain_cat
    GrayInterchangerCodomain_cat
    gray_interchanger_lhs_func
    gray_interchanger_rhs_func
    gray_interchanger_base_identity
    gray_interchanger_transf;

/*
  Retain the next off-diagonal hom action.  Its identity object computes to
  gray_interchanger, so the public surface has not capped the internal action
  one dimension too early.
*/
symbol gray_interchanger_next_func
  : τ (Functor
      (Hom_cat
        GrayInterchangerDomain_cat
        gray_interchanger_base_identity
        gray_interchanger_base_identity)
      (Hom_cat
        GrayInterchangerCodomain_cat
        gray_interchanger_source
        gray_interchanger_target))
≔ @tapp1_func
    GrayInterchangerDomain_cat
    GrayInterchangerCodomain_cat
    gray_interchanger_lhs_func
    gray_interchanger_rhs_func
    gray_interchanger_base_identity
    gray_interchanger_base_identity
    gray_interchanger_transf;
