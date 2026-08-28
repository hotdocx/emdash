/*
  Reviewer example: Yoneda standard semicubes decode internally to the native
  arbitrary-dimensional {L,R,*} face action.
*/

require open emdash.emdash3_2_semicubical_representables;

// A p-face of the standard n-semicube is precisely a public face code.
assert
  (p n : τ (Obj SemiCubePlus_cat)) ⊢
  @standard_semicube_level n p
  ≡ Hom_cat SemiCubePlus_cat p n;

// Decoder object action is the whole semicubical-nerve action.
assert [C : Cat]
  (p n : τ (Obj SemiCubePlus_cat))
  (f : τ (@CubeFaceCode p n)) ⊢
  @fapp0
    (@standard_semicube_level n p)
    (Functor_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
    (@standard_semicube_native_decode_func C p n)
    f
  ≡ @semicubical_nerve_action_func C n p f;

// Its selected comparison reaches the computing profile-retaining action.
assert [C : Cat]
  (p n : τ (Obj SemiCubePlus_cat))
  (f : τ (@CubeFaceCode p n)) ⊢
  @standard_semicube_native_decode_path C p n f
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@fapp0
        (@standard_semicube_level n p)
        (Functor_cat
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C p))
        (@standard_semicube_native_decode_func C p n)
        f)
      (@cube_face_action_func C p n f));

// The comparison is not capped at objects: the whole next Hom action exists.
type @standard_semicube_native_decode_hom_func;
