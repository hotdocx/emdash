/*
  Reviewer for the directed interchanger of the profiled Gray walking square.
*/

require open emdash.emdash3_2_gray_interchanger;

// The right-closure target now carries the confirmed lax profile name.
assert [A B C : Cat] ⊢
  @GrayRightTarget A B C
  ≡ @GrayHom_lax A (@GrayHom_lax B C);

// The square's two readable boundary composites inhabit the common corner.
assert ⊢
  gray_square_post_composite
  : τ (Obj GrayInterchangerCodomain_cat);

assert ⊢
  gray_square_pre_composite
  : τ (Obj GrayInterchangerCodomain_cat);

// The whole owner is exactly the active post/left laxity transformation.
assert ⊢
  gray_interchanger_transf
  ≡ @tapp1_post_laxity_transf
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      gray_square_outer_transf
      walking_arrow_src
      walking_arrow_src
      walking_arrow_tgt
      walking_arrow_generator;

// Its identity component is the existing extracted laxity cell.
assert ⊢
  gray_interchanger
  ≡ @tapp1_post_laxity_cell
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      gray_square_outer_transf
      walking_arrow_src
      walking_arrow_src
      walking_arrow_tgt
      walking_arrow_generator
      (@id WalkingArrow_cat walking_arrow_src);

// The retained next owner remains the generic whole transformation action.
assert ⊢
  gray_interchanger_next_func
  ≡ @tapp1_func
      GrayInterchangerDomain_cat
      GrayInterchangerCodomain_cat
      gray_interchanger_lhs_func
      gray_interchanger_rhs_func
      gray_interchanger_base_identity
      gray_interchanger_base_identity
      gray_interchanger_transf;

// Evaluating that next owner at the identity recovers the interchanger.
assert ⊢
  @fapp0
    (Hom_cat
      GrayInterchangerDomain_cat
      gray_interchanger_base_identity
      gray_interchanger_base_identity)
    (Hom_cat
      GrayInterchangerCodomain_cat
      gray_interchanger_source
      gray_interchanger_target)
    gray_interchanger_next_func
    (@id
      GrayInterchangerDomain_cat
      gray_interchanger_base_identity)
  ≡ gray_interchanger;

// The extracted cell is not collapsed by the prototype's endpoint cuts.
assertnot ⊢
  gray_interchanger
  ≡ @id GrayInterchangerCodomain_cat gray_interchanger_source;

// Its post/left provenance remains distinct from the pre/right mirror.
assertnot ⊢
  gray_interchanger
  ≡ @tapp1_pre_laxity_cell
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      gray_square_outer_transf
      walking_arrow_src
      walking_arrow_tgt
      walking_arrow_tgt
      walking_arrow_generator
      (@id WalkingArrow_cat walking_arrow_tgt);
