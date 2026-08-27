/* Reviewer example: native variable-dimensional {L,R,*} face action. */

require open emdash.emdash3_2_semicubical_face_action;

// The two dimension-one endpoint codes compute to whole source and target.
symbol cube_action_left_0_1
  : τ (@CubeFaceCode zero (succ zero))
≔ @cube_face_left zero zero cube_face_nil;

symbol cube_action_right_0_1
  : τ (@CubeFaceCode zero (succ zero))
≔ @cube_face_right zero zero cube_face_nil;

assert [C : Cat] ⊢
  @cube_face_action_func C zero (succ zero) cube_action_left_0_1
  ≡ @cubical_src_func C;

assert [C : Cat] ⊢
  @cube_face_action_func C zero (succ zero) cube_action_right_0_1
  ≡ @cubical_tgt_func C;

// Star lifts the older action through CubicalArrow with its retained property.
assert [C : Cat] ⊢
  @cube_face_action_func
    C (succ zero) (succ zero)
    (@cube_face_identity (succ zero))
  ≡ @CubicalArrow_func
      C C
      (@id_func C)
      (@identity_is_pseudo C);

// The two inner edge faces are recursively lifted L/R actions. Their property
// proofs retain the recursive construction rather than being silently
// replaced by independently selected square-face proofs.
symbol cube_action_inner_left_1_2
  : τ (@CubeFaceCode
      (succ zero)
      (succ (succ zero)))
≔ @cube_face_keep
    zero (succ zero)
    cube_action_left_0_1;

symbol cube_action_inner_right_1_2
  : τ (@CubeFaceCode
      (succ zero)
      (succ (succ zero)))
≔ @cube_face_keep
    zero (succ zero)
    cube_action_right_0_1;

assert [C : Cat] ⊢
  @cube_face_action_func
    C (succ zero) (succ (succ zero))
    cube_action_inner_left_1_2
  ≡ @CubicalArrow_func
      (@CubicalArrow_cat C) C
      (@cube_face_action_func C zero (succ zero) cube_action_left_0_1)
      (@cube_face_action_is_pseudo C zero (succ zero) cube_action_left_0_1);

assert [C : Cat] ⊢
  @cube_face_action_func
    C (succ zero) (succ (succ zero))
    cube_action_inner_right_1_2
  ≡ @CubicalArrow_func
      (@CubicalArrow_cat C) C
      (@cube_face_action_func C zero (succ zero) cube_action_right_0_1)
      (@cube_face_action_is_pseudo C zero (succ zero) cube_action_right_0_1);

/*
  An outer face retains action(*) before source/target. It is not collapsed to
  the fixed square-face owner until the later whole identity law is supplied.
*/
symbol cube_action_outer_left_1_2
  : τ (@CubeFaceCode
      (succ zero)
      (succ (succ zero)))
≔ @cube_face_left
    (succ zero) (succ zero)
    (@cube_face_identity (succ zero));

assert [C : Cat] ⊢
  @cube_face_action_func
    C (succ zero) (succ (succ zero))
    cube_action_outer_left_1_2
  ≡ @comp_cat_fapp0
      (@CubicalSquare_cat C)
      (@CubicalArrow_cat C)
      (@CubicalArrow_cat C)
      (@CubicalArrow_func
        C C
        (@id_func C)
        (@identity_is_pseudo C))
      (@cubical_src_func (@CubicalArrow_cat C));

// Every action retains the property for another star step.
assert [C : Cat]
  (p n : τ Nat_grpd)
  (f : τ (@CubeFaceCode p n)) ⊢
  @cube_face_action_is_pseudo C p n f
  : τ (@IsPseudoFunctor
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p)
      (@cube_face_action_func C p n f));

// The whole action remains iterable at the next hom level.
type @fapp1_func
  (@CubicalLevel_cat Cat_cat (succ zero))
  (@CubicalLevel_cat Cat_cat zero)
  (@cube_face_action_func
    Cat_cat zero (succ zero) cube_action_left_0_1);

// Intrinsic indices still reject a point code as an edge-level endomorphism.
assertnot ⊢
  cube_action_left_0_1
  : τ (@CubeFaceCode (succ zero) (succ zero));
