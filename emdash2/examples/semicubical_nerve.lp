/* Reviewer example: whole native semicubical nerve and action laws. */

require open emdash.emdash3_2_semicubical_nerve;

// The whole nerve classifies native cubical levels at every dimension.
assert [C : Cat] (n : τ Nat_grpd) ⊢
  @fapp0
    (Op_cat SemiCubePlus_cat) Cat_cat
    (@semicubical_nerve_func C) n
  ≡ @CubicalLevel_cat C n;

assert [C : Cat] ⊢
  @fapp0
    (Op_cat SemiCubePlus_cat) Cat_cat
    (@semicubical_nerve_func C) (succ (succ zero))
  ≡ @CubicalSquare_cat C;

// Arrow computation is a typed whole comparison, not a competing runtime beta.
assert [C : Cat]
  (p n : τ Nat_grpd)
  (f : τ (@CubeFaceCode p n)) ⊢
  @semicubical_nerve_action_path C n p f
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@semicubical_nerve_action_func C n p f)
      (@cube_face_action_func C p n f));

assertnot [C : Cat]
  (p n : τ Nat_grpd)
  (f : τ (@CubeFaceCode p n)) ⊢
  @semicubical_nerve_action_func C n p f
  ≡ @cube_face_action_func C p n f;

// Named public substitution agrees propositionally with arbitrary category
// composition; no broad runtime category fold is required.
assert (p q n : τ Nat_grpd)
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q)) ⊢
  @semi_cube_plus_comp_public_path p q n g f
  : τ (@=
      (@CubeFaceCode p n)
      (@cube_face_comp p q n g f)
      (@comp_fapp0 SemiCubePlus_cat p q n g f));

// The all-star action is propositionally the whole identity.
assert [C : Cat] (n : τ Nat_grpd) ⊢
  @cube_face_action_identity_path C n
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n))
      (@cube_face_action_func C n n (@cube_face_identity n))
      (@id_func (@CubicalLevel_cat C n)));

// Structural substitution acts contravariantly in every dimension.
assert [C : Cat]
  (p q n : τ Nat_grpd)
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q)) ⊢
  @cube_face_action_comp_path C p q n g f
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@cube_face_action_func C p n (@cube_face_comp p q n g f))
      (@comp_cat_fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C q)
        (@CubicalLevel_cat C p)
        (@cube_face_action_func C p q f)
        (@cube_face_action_func C q n g)));

// The whole nerve retains action on paths between face codes and all higher
// transformations supplied by the generic functor calculus.
type @fapp1_func
  (Op_cat SemiCubePlus_cat)
  Cat_cat
  (@semicubical_nerve_func Cat_cat);
