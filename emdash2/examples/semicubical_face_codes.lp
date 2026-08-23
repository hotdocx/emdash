/*
  Reviewer example: augmented semicubical {L,R,*} face-map codes.

  Raw syntax owns structural substitution. Public codes are classified sets;
  their visible constructors and composition still compute through the
  restricted truncation recursor. The internal semicube category is a later
  layer.
*/

require open emdash.emdash3_2_semicubical_face_codes;

// Every public code carrier is intrinsically a set.
assert (p n : τ Nat_grpd) ⊢
  @cube_face_code_is_set p n
  : τ (IsSetGrpd (@CubeFaceCode p n));

// Public constructors retain their raw point computation.
assert ⊢
  @cube_face_left zero zero cube_face_nil
  ≡ @trunc_intro
      trunc_zero
      (@RawCubeFaceCode zero (succ zero))
      (@raw_cube_left zero zero raw_cube_nil);

assert ⊢
  @cube_face_right zero zero cube_face_nil
  ≡ @trunc_intro
      trunc_zero
      (@RawCubeFaceCode zero (succ zero))
      (@raw_cube_right zero zero raw_cube_nil);

assert ⊢
  @cube_face_keep zero zero cube_face_nil
  ≡ @trunc_intro
      trunc_zero
      (@RawCubeFaceCode (succ zero) (succ zero))
      (@raw_cube_keep zero zero raw_cube_nil);

// Identity is the all-star word.
assert ⊢ @cube_face_identity zero ≡ cube_face_nil;

assert ⊢
  @cube_face_identity (succ zero)
  ≡ @cube_face_keep zero zero cube_face_nil;

// The two endpoint inclusions of the directed one-cube.
symbol cube_left_0_1
  : τ (@CubeFaceCode zero (succ zero))
≔ @cube_face_left zero zero cube_face_nil;

symbol cube_right_0_1
  : τ (@CubeFaceCode zero (succ zero))
≔ @cube_face_right zero zero cube_face_nil;

assertnot ⊢ cube_left_0_1 ≡ cube_right_0_1;

// Outer star consumes the inner fixed-coordinate choice.
assert ⊢
  @cube_face_comp
    zero (succ zero) (succ zero)
    (@cube_face_identity (succ zero))
    cube_left_0_1
  ≡ cube_left_0_1;

assert ⊢
  @cube_face_comp
    zero (succ zero) (succ zero)
    (@cube_face_identity (succ zero))
    cube_right_0_1
  ≡ cube_right_0_1;

// Outer fixed coordinates pass through without consuming the inner code.
symbol cube_x_left_1_2
  : τ (@CubeFaceCode (succ zero) (succ (succ zero)))
≔ @cube_face_left
    (succ zero) (succ zero)
    (@cube_face_identity (succ zero));

assert ⊢
  @cube_face_comp
    zero (succ zero) (succ (succ zero))
    cube_x_left_1_2
    cube_right_0_1
  ≡ @cube_face_left
      zero (succ zero)
      (@cube_face_right zero zero cube_face_nil);

// A closed 0 -> 1 -> 2 -> 3 chain validates both substitution orders.
symbol cube_right_x_1_2
  : τ (@CubeFaceCode (succ zero) (succ (succ zero)))
≔ @cube_face_keep
    zero (succ zero)
    (@cube_face_right zero zero cube_face_nil);

symbol cube_x_left_x_2_3
  : τ (@CubeFaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @cube_face_keep
    (succ zero) (succ (succ zero))
    (@cube_face_left
      (succ zero) (succ zero)
      (@cube_face_identity (succ zero)));

assert ⊢
  @cube_face_comp
    zero
    (succ (succ zero))
    (succ (succ (succ zero)))
    cube_x_left_x_2_3
    (@cube_face_comp
      zero
      (succ zero)
      (succ (succ zero))
      cube_right_x_1_2
      cube_left_0_1)
  ≡ @cube_face_comp
      zero
      (succ zero)
      (succ (succ (succ zero)))
      (@cube_face_comp
        (succ zero)
        (succ (succ zero))
        (succ (succ (succ zero)))
        cube_x_left_x_2_3
        cube_right_x_1_2)
      cube_left_0_1;

// Intrinsic indices reject a point code where an edge code is required.
assertnot ⊢
  cube_left_0_1
  : τ (@CubeFaceCode (succ zero) (succ zero));
