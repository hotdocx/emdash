/* Reviewer example: recursive immediate boundary frames in dimensions 1–3. */

require open emdash.emdash3_2_semicubical_frames;

// The recurrence exposes 0, 2, 4, and 6 immediate faces.
assert ⊢ @CubeImmediateFaceCount zero ≡ zero;

assert ⊢
  @CubeImmediateFaceCount (succ zero)
  ≡ succ (succ zero);

assert ⊢
  @CubeImmediateFaceCount (succ (succ zero))
  ≡ succ (succ (succ (succ zero)));

assert ⊢
  @CubeImmediateFaceCount (succ (succ (succ zero)))
  ≡ succ (succ (succ (succ (succ (succ zero)))));

// In every positive dimension, the first pair is the new L/R coordinate.
assert (n : τ Nat_grpd) ⊢
  @cube_immediate_new_left_observation_path n
  : τ (@=
      (@CubeFaceCode n (succ n))
      (@cube_immediate_new_left_observation n)
      (@cube_new_left_face_code n));

assert (n : τ Nat_grpd) ⊢
  @cube_immediate_new_right_observation_path n
  : τ (@=
      (@CubeFaceCode n (succ n))
      (@cube_immediate_new_right_observation n)
      (@cube_new_right_face_code n));

// Removing that pair leaves precisely the star-lifted older family.
assert (n : τ Nat_grpd) ⊢
  @cube_immediate_inherited_face_codes_path n
  : τ (@=
      (@FiniteFamily
        (@CubeFaceCode (succ n) (succ (succ n)))
        (@CubeImmediateFaceCount (succ n)))
      (@cube_immediate_inherited_face_codes n)
      (@finite_family_map
        (@CubeFaceCode n (succ n))
        (@CubeFaceCode (succ n) (succ (succ n)))
        (λ f : τ (@CubeFaceCode n (succ n)),
          @cube_face_keep n (succ n) f)
        (@CubeImmediateFaceCount (succ n))
        (@cube_immediate_face_codes n)));

// Four closed cofaces of a square, in the generic family order.
symbol square_frame_outer_left
  : τ (@CubeFaceCode (succ zero) (succ (succ zero)))
≔ @cube_new_left_face_code (succ zero);

symbol square_frame_outer_right
  : τ (@CubeFaceCode (succ zero) (succ (succ zero)))
≔ @cube_new_right_face_code (succ zero);

symbol square_frame_inner_left
  : τ (@CubeFaceCode (succ zero) (succ (succ zero)))
≔ @cube_face_keep
    zero (succ zero) (@cube_new_left_face_code zero);

symbol square_frame_inner_right
  : τ (@CubeFaceCode (succ zero) (succ (succ zero)))
≔ @cube_face_keep
    zero (succ zero) (@cube_new_right_face_code zero);

// On a visible square, those four actions recover its four independent edges.
assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalLevel_cat C (succ (succ zero)))
    (@CubicalLevel_cat C (succ zero))
    (@cube_face_action_func
      C (succ zero) (succ (succ zero)) square_frame_outer_left)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C x1 x2 u;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalLevel_cat C (succ (succ zero)))
    (@CubicalLevel_cat C (succ zero))
    (@cube_face_action_func
      C (succ zero) (succ (succ zero)) square_frame_outer_right)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C y1 y2 v;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalLevel_cat C (succ (succ zero)))
    (@CubicalLevel_cat C (succ zero))
    (@cube_face_action_func
      C (succ zero) (succ (succ zero)) square_frame_inner_left)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C x1 y1 a;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalLevel_cat C (succ (succ zero)))
    (@CubicalLevel_cat C (succ zero))
    (@cube_face_action_func
      C (succ zero) (succ (succ zero)) square_frame_inner_right)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C x2 y2 b;

// A cube is a visible successor edge theta:S->T at level two. New L/R recover
// S/T propositionally; every one of the four older square codes star-lifts to
// the corresponding side-square object.
assert [C : Cat]
  (S T : τ (Obj (@CubicalLevel_cat C (succ (succ zero)))))
  (theta : τ (Hom (@CubicalLevel_cat C (succ (succ zero))) S T)) ⊢
  @cube_new_left_face_at_path
    C (succ (succ zero))
    (@cubical_edge (@CubicalLevel_cat C (succ (succ zero))) S T theta)
  : τ (@=
      (Obj (@CubicalLevel_cat C (succ (succ zero))))
      (@fapp0
        (@CubicalLevel_cat C (succ (succ (succ zero))))
        (@CubicalLevel_cat C (succ (succ zero)))
        (@cube_face_action_func
          C
          (succ (succ zero))
          (succ (succ (succ zero)))
          (@cube_new_left_face_code (succ (succ zero))))
        (@cubical_edge
          (@CubicalLevel_cat C (succ (succ zero))) S T theta))
      S);

assert [C : Cat]
  (f : τ (@CubeFaceCode
    (succ zero) (succ (succ zero))))
  (S T : τ (Obj (@CubicalLevel_cat C (succ (succ zero)))))
  (theta : τ (Hom (@CubicalLevel_cat C (succ (succ zero))) S T)) ⊢
  @cube_keep_face_at_path
    C (succ zero) (succ (succ zero)) f S T theta
  : τ (@=
      (Obj (@CubicalLevel_cat C (succ (succ zero))))
      (@fapp0
        (@CubicalLevel_cat C (succ (succ (succ zero))))
        (@CubicalLevel_cat C (succ (succ zero)))
        (@cube_face_action_func
          C
          (succ (succ zero))
          (succ (succ (succ zero)))
          (@cube_face_keep
            (succ zero) (succ (succ zero)) f))
        (@cubical_edge
          (@CubicalLevel_cat C (succ (succ zero))) S T theta))
      (@cubical_edge
        (@CubicalLevel_cat C (succ zero))
        (@fapp0
          (@CubicalLevel_cat C (succ (succ zero)))
          (@CubicalLevel_cat C (succ zero))
          (@cube_face_action_func
            C (succ zero) (succ (succ zero)) f)
          S)
        (@fapp0
          (@CubicalLevel_cat C (succ (succ zero)))
          (@CubicalLevel_cat C (succ zero))
          (@cube_face_action_func
            C (succ zero) (succ (succ zero)) f)
          T)
        (@fapp1_fapp0
          (@CubicalLevel_cat C (succ (succ zero)))
          (@CubicalLevel_cat C (succ zero))
          (@cube_face_action_func
            C (succ zero) (succ (succ zero)) f)
          S T theta)));
