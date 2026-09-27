/* Reviewer example: whole semicubical nerve and Yoneda beta for path cubes. */

require open emdash.emdash3_2_path_cubical_nerve;

// The whole nerve computes at every level to the existing Path specialization.
assert [A : Grpd]
  (n : τ (Obj SemiCubePlus_cat)) ⊢
  @fapp0
    (Op_cat SemiCubePlus_cat)
    Cat_cat
    (@path_semicubical_nerve_func A)
    n
  ≡ @PathCubicalLevel_cat A n;

// Every public face code acts through one whole native restriction functor.
assert [A : Grpd]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n)) ⊢
  @path_cube_face_action_func A p n f
  : τ (Functor
      (@PathCubicalLevel_cat A n)
      (@PathCubicalLevel_cat A p));

// The variable-dimensional family exposes all immediate faces.
assert [A : Grpd]
  (n : τ Nat_grpd) ⊢
  @path_cube_immediate_face_actions A n
  : τ (@FiniteFamily
      (Functor
        (@PathCubicalLevel_cat A (succ n))
        (@PathCubicalLevel_cat A n))
      (@CubeImmediateFaceCount (succ n)));

// Counts recover two edge endpoints, four square edges, and six cube faces.
assert ⊢ @CubeImmediateFaceCount (succ zero)
  ≡ succ (succ zero);

assert ⊢ @CubeImmediateFaceCount (succ (succ zero))
  ≡ succ (succ (succ (succ zero)));

assert ⊢ @CubeImmediateFaceCount (succ (succ (succ zero)))
  ≡ succ (succ (succ (succ (succ (succ zero)))));

// The representable decoder is the existing whole face action at Path(A).
assert [A : Grpd]
  (p n : τ (Obj SemiCubePlus_cat)) ⊢
  @path_standard_semicube_native_decode_func A p n
  ≡ @standard_semicube_native_decode_func (Path_cat A) p n;

// A native path cube gives a whole representable map and evaluates back.
assert [A : Grpd]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (@PathCube_grpd A n)) ⊢
  @path_cubical_yoneda_section A n X
  : τ (Hom
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube n)
      (@path_semicubical_nerve_func A));

assert [A : Grpd]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (@PathCube_grpd A n)) ⊢
  @path_cubical_yoneda_beta A n X
  : τ (@=
      (@PathCube_grpd A n)
      (@path_cubical_yoneda_eval
        A n (@path_cubical_yoneda_section A n X))
      X);

type @path_semicubical_nerve_func;
type @path_cube_face_action_func;
type @path_cube_immediate_face_actions;
type @path_cubical_yoneda_beta;
