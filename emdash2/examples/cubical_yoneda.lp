/* Reviewer example: object-level Yoneda realization of native n-cubes. */

require open emdash.emdash3_2_cubical_yoneda;

// A native cube supplies one whole map from the representable standard cube.
assert [C : Cat]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (Obj (@CubicalLevel_cat C n))) ⊢
  @cubical_yoneda_section C n X
  : τ (Hom
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube n)
      (@semicubical_nerve_func C));

// Evaluation of the selected section is the native identity-face action.
assert [C : Cat]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (Obj (@CubicalLevel_cat C n))) ⊢
  @cubical_yoneda_eval C n (@cubical_yoneda_section C n X)
  ≡ @fapp0
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C n)
      (@semicubical_nerve_action_func C n n (@cube_face_identity n))
      X;

// The selected beta is inherited from whole nerve functoriality.
assert [C : Cat]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (Obj (@CubicalLevel_cat C n))) ⊢
  @cubical_yoneda_beta C n X
  : τ (@=
      (Obj (@CubicalLevel_cat C n))
      (@cubical_yoneda_eval C n (@cubical_yoneda_section C n X))
      X);

type @cubical_yoneda_section;
type @cubical_yoneda_eval;
type @cubical_yoneda_beta;
