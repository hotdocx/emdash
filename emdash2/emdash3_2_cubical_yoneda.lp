/*
  Emdash v3.2: object-level Yoneda realization of native semicubical cells.

  A native n-cube X selects the existing represented covariance section

    StandardSemicube(n) -> semicubical_nerve_func(C).

  Conversely, evaluate any such whole presheaf map at level n and the public
  all-star identity face. Evaluation of the selected section is the whole
  nerve action at that identity; evaluating generic functoriality's identity
  path gives the object beta back to X.

  This module is transparent and rule-free. It claims neither the eta law nor
  a whole equivalence and adds no pointwise naturality family.
*/

require open emdash.emdash3_2_cubical;

// Whole Yoneda section selected by one native n-cube.
symbol cubical_yoneda_section
  [C : Cat]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (Obj (@CubicalLevel_cat C n)))
  : τ (Hom
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube n)
      (@semicubical_nerve_func C))
≔ @fib_cov_transf
    (Op_cat SemiCubePlus_cat)
    (@semicubical_nerve_func C)
    n
    X;

// Evaluate a representable map at its identity face.
symbol cubical_yoneda_eval
  [C : Cat]
  [n : τ (Obj SemiCubePlus_cat)]
  (eta : τ (Hom
    (@Psh_cat SemiCubePlus_cat)
    (@StandardSemicube n)
    (@semicubical_nerve_func C)))
  : τ (Obj (@CubicalLevel_cat C n))
≔ @fapp0
    (Fibre_cat (@StandardSemicube n) n)
    (Fibre_cat (@semicubical_nerve_func C) n)
    (@Fibre_func
      (Op_cat SemiCubePlus_cat)
      (@StandardSemicube n)
      (@semicubical_nerve_func C)
      eta
      n)
    (@cube_face_identity n);

// Selected object beta: evaluation of the whole native nerve's identity law.
symbol cubical_yoneda_beta
  [C : Cat]
  [n : τ (Obj SemiCubePlus_cat)]
  (X : τ (Obj (@CubicalLevel_cat C n)))
  : τ (@=
      (Obj (@CubicalLevel_cat C n))
      (@cubical_yoneda_eval C n (@cubical_yoneda_section C n X))
      X)
≔ @eq_ap
    (Hom Cat_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C n))
    (Obj (@CubicalLevel_cat C n))
    (λ F : τ (Functor
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n)),
      @fapp0
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C n)
        F X)
    (@semicubical_nerve_action_func C n n (@cube_face_identity n))
    (@id_func (@CubicalLevel_cat C n))
    (@fapp1_id_path
      (Op_cat SemiCubePlus_cat)
      Cat_cat
      (@semicubical_nerve_func C)
      n);
