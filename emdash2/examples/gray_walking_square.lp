/*
  Reviewer example: the four vertices and coordinate arrows of I tensor I.

  Every boundary term is obtained from right coevaluation and the existing
  whole walking-arrow generator.  The example deliberately stops before the
  interchanger, which is the next focused tranche.
*/

require open emdash.emdash3_2_gray_walking_square;

assert ⊢
  GrayWalkingSquare_cat
  ≡ @GrayTensor_R WalkingArrow_cat WalkingArrow_cat;

// Coevaluation at the outer endpoints produces the two strict inner codes.
assert ⊢
  gray_square_inner_src_data
  ≡ @fapp0
      WalkingArrow_cat
      (@GrayHom_lax WalkingArrow_cat GrayWalkingSquare_cat)
      (@gray_coevaluation_R_func WalkingArrow_cat WalkingArrow_cat)
      walking_arrow_src;

assert ⊢
  gray_square_inner_tgt_data
  ≡ @fapp0
      WalkingArrow_cat
      (@GrayHom_lax WalkingArrow_cat GrayWalkingSquare_cat)
      (@gray_coevaluation_R_func WalkingArrow_cat WalkingArrow_cat)
      walking_arrow_tgt;

// Their endpoint evaluations are the four square vertices.
assert ⊢ gray_square_obj00 : τ (Obj GrayWalkingSquare_cat);
assert ⊢ gray_square_obj01 : τ (Obj GrayWalkingSquare_cat);
assert ⊢ gray_square_obj10 : τ (Obj GrayWalkingSquare_cat);
assert ⊢ gray_square_obj11 : τ (Obj GrayWalkingSquare_cat);

// Both inner coordinate edges retain whole Terminal-indexed owners.
assert ⊢
  gray_square_inner_src_generator_func
  : τ (Functor
      Terminal_cat
      (Hom_cat
        GrayWalkingSquare_cat
        gray_square_obj00
        gray_square_obj01));

assert ⊢
  gray_square_inner_tgt_generator_func
  : τ (Functor
      Terminal_cat
      (Hom_cat
        GrayWalkingSquare_cat
        gray_square_obj10
        gray_square_obj11));

assert ⊢
  gray_square_inner_src_arrow
  ≡ @fapp1_fapp0
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      walking_arrow_src
      walking_arrow_tgt
      walking_arrow_generator;

assert ⊢
  gray_square_inner_tgt_arrow
  ≡ @fapp1_fapp0
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_tgt_func
      walking_arrow_src
      walking_arrow_tgt
      walking_arrow_generator;

// The outer coordinate is one whole coevaluation-generated transformation.
assert ⊢
  gray_square_outer_transf
  ≡ @fapp1_fapp0
      WalkingArrow_cat
      (@GrayHom_lax WalkingArrow_cat GrayWalkingSquare_cat)
      (@gray_coevaluation_R_func WalkingArrow_cat WalkingArrow_cat)
      walking_arrow_src
      walking_arrow_tgt
      walking_arrow_generator;

assert ⊢
  gray_square_outer_src_eval_func
  ≡ @tapp0_func
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      walking_arrow_src;

assert ⊢
  gray_square_outer_tgt_eval_func
  ≡ @tapp0_func
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      walking_arrow_tgt;

assert ⊢
  gray_square_outer_src_arrow
  ≡ @tapp0_fapp0
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      walking_arrow_src
      gray_square_outer_transf;

assert ⊢
  gray_square_outer_tgt_arrow
  ≡ @tapp0_fapp0
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      walking_arrow_tgt
      gray_square_outer_transf;

// The four vertex normal forms remain pairwise distinct.
assertnot ⊢ gray_square_obj00 ≡ gray_square_obj01;
assertnot ⊢ gray_square_obj00 ≡ gray_square_obj10;
assertnot ⊢ gray_square_obj00 ≡ gray_square_obj11;
assertnot ⊢ gray_square_obj01 ≡ gray_square_obj10;
assertnot ⊢ gray_square_obj01 ≡ gray_square_obj11;
assertnot ⊢ gray_square_obj10 ≡ gray_square_obj11;

// The concrete right tensor does not collapse to the Cartesian square.
assertnot ⊢
  GrayWalkingSquare_cat
  ≡ @Product_cat WalkingArrow_cat WalkingArrow_cat;
