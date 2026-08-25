/*
  Reviewer example: the right-Gray cube decoder is one internal Nat recursion,
  uniform in the ambient category.  Its public index n denotes geometric
  dimension n+1.
*/

require open emdash.emdash3_2_gray_cube_decoder;

// The level shift begins by reflexivity and remains internal at successors.
assert [C : Cat] ⊢
  @cubical_level_shift_path C zero
  ≡ @eq_refl
      (Obj Cat_cat)
      (@CubicalLevel_cat (@LaxArrow_cat C) (succ zero));

// Dimension one is literal walking-arrow evaluation.
assert [C : Cat]
  (H : τ (@StrictFunctorData WalkingArrow_cat C)) ⊢
  @gray_cube_observation C zero H
  ≡ @gray_cube_decode_one C H;

// The variable successor is exactly curry, graph, recursive decode, and shift.
assert [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctorData (@GrayCubePos_R (succ n)) C)) ⊢
  @gray_cube_observation C (succ n) H
  ≡ @gray_cube_decode_step
      n (@gray_cube_observation_all n) C H;

// Selected dimensions one through three have the native cubical classifiers.
assert [C : Cat]
  (H : τ (@StrictFunctorData GrayCube1_R C)) ⊢
  @gray_cube_observation C zero H
  : τ (Obj (@CubicalLevel_cat C (succ zero)));

assert [C : Cat]
  (H : τ (@StrictFunctorData GrayCube2_R C)) ⊢
  @gray_cube_observation C (succ zero) H
  : τ (Obj (@CubicalLevel_cat C (succ (succ zero))));

assert [C : Cat]
  (H : τ (@StrictFunctorData GrayCube3_R C)) ⊢
  @gray_cube_observation C (succ (succ zero)) H
  : τ (Obj
      (@CubicalLevel_cat C (succ (succ (succ zero)))));

// The successor graph keeps a strict code and a first-class readable carrier
// path to the transparent whole transformation graph.
assert [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctorData (@GrayCubePos_R (succ n)) C)) ⊢
  @strict_gray_transf_graph_carrier_path
    (@GrayCubePos_R n)
    C
    (@gray_cube_step_source_data C n H)
    (@gray_cube_step_target_data C n H)
    (@gray_cube_step_transf C n H)
  : τ (@=
      (Functor (@GrayCubePos_R n) (@LaxArrow_cat C))
      (@strict_functor_carrier
        (@GrayCubePos_R n)
        (@LaxArrow_cat C)
        (@gray_cube_step_graph_data C n H))
      (@gray_transf_graph_func
        (@GrayCubePos_R n)
        C
        (@strict_functor_carrier
          (@GrayCubePos_R n) C
          (@gray_cube_step_source_data C n H))
        (@strict_functor_carrier
          (@GrayCubePos_R n) C
          (@gray_cube_step_target_data C n H))
        (@gray_cube_step_transf C n H)));

// For the identity realization of I tensor_R I, the successor inputs recover
// the already-established walking-square coevaluation data.
assert ⊢
  @gray_cube_step_curry_data
    GrayWalkingSquare_cat zero
    (@strict_identity_data GrayWalkingSquare_cat)
  ≡ @gray_coevaluation_R_data WalkingArrow_cat WalkingArrow_cat;

assert ⊢
  @gray_cube_step_source_data
    GrayWalkingSquare_cat zero
    (@strict_identity_data GrayWalkingSquare_cat)
  ≡ gray_square_inner_src_data;

assert ⊢
  @gray_cube_step_target_data
    GrayWalkingSquare_cat zero
    (@strict_identity_data GrayWalkingSquare_cat)
  ≡ gray_square_inner_tgt_data;

assert ⊢
  @gray_cube_step_transf
    GrayWalkingSquare_cat zero
    (@strict_identity_data GrayWalkingSquare_cat)
  ≡ gray_square_outer_transf;
