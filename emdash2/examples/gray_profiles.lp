/*
  Reviewer example: computational strict-functor codes and the selected
  strict-object/lax-arrow Gray-hom profile.
*/

require open emdash.emdash3_2_gray_profiles;

// Rigid ambient negative control, deliberately outside StrictFunctorData.
injective symbol example_unprofiled_functor
  (A B : Cat)
  : τ (Functor A B);

assert [A B : Cat]
  (S : τ (@StrictFunctorData A B)) ⊢
  S : τ (Obj (@GrayHom_oplax A B));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_oplax A B))) ⊢
  Hom_cat (@GrayHom_oplax A B) X Y
  ≡ @Transf_cat
      A B
      (@strict_functor_carrier A B X)
      (@strict_functor_carrier A B Y);

assert [A B : Cat]
  (X : τ (Obj (@GrayHom_oplax A B))) ⊢
  @fapp0
    (@GrayHom_oplax A B)
    (@Functor_cat A B)
    (@grayhom_oplax_include_func A B)
    X
  ≡ @strict_functor_carrier A B X;

// Identity and composition delegate to the shared ambient transfor tower.
assert [A B : Cat]
  (X : τ (Obj (@GrayHom_oplax A B))) ⊢
  @id (@GrayHom_oplax A B) X
  : τ (Hom
      (@Functor_cat A B)
      (@strict_functor_carrier A B X)
      (@strict_functor_carrier A B X));

assert [A B : Cat]
  (X Y Z : τ (Obj (@GrayHom_oplax A B)))
  (g : τ (Hom (@GrayHom_oplax A B) Y Z))
  (f : τ (Hom (@GrayHom_oplax A B) X Y)) ⊢
  @comp_fapp0 (@GrayHom_oplax A B) X Y Z g f
  : τ (Hom
      (@Functor_cat A B)
      (@strict_functor_carrier A B X)
      (@strict_functor_carrier A B Z));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_oplax A B))) ⊢
  @fapp1_func
    (@GrayHom_oplax A B)
    (@Functor_cat A B)
    (@grayhom_oplax_include_func A B)
    X Y
  ≡ @id_func
      (@Transf_cat
        A B
        (@strict_functor_carrier A B X)
        (@strict_functor_carrier A B Y));

// The next hom is the existing modification/higher-cell category.
assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_oplax A B)))
  (eta theta : τ (Hom (@GrayHom_oplax A B) X Y)) ⊢
  Hom_cat
    (Hom_cat (@GrayHom_oplax A B) X Y)
    eta theta
  ≡ Hom_cat
      (@Transf_cat
        A B
        (@strict_functor_carrier A B X)
        (@strict_functor_carrier A B Y))
      eta theta;

assert [A : Cat] ⊢
  @strict_identity_data A
  : τ (Obj (@GrayHom_oplax A A));

assert [A : Cat] ⊢
  @strict_identity_carrier_path A
  : τ (@=
      (Functor A A)
      (@strict_functor_carrier A A (@strict_identity_data A))
      (@id_func A));

// A decoded strict code makes the generic extracted compositor identity.
assert [A B : Cat]
  (S : τ (@StrictFunctorData A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @fapp1_compositor
    A B (@strict_functor_carrier A B S)
    X Y Z g f
  ≡ @id
      (Hom_cat
        B
        (@fapp0 A B (@strict_functor_carrier A B S) X)
        (@fapp0 A B (@strict_functor_carrier A B S) Z))
      (@strict_functor_compositor_lhs
        A B (@strict_functor_carrier A B S)
        X Y Z g f);

// The strict specialization does not leak to a rigid ambient functor.
assertnot [A B : Cat]
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @fapp1_compositor
    A B (@example_unprofiled_functor A B) X Y Z g f
  ≡ @id
      (Hom_cat
        B
        (@fapp0 A B (@example_unprofiled_functor A B) X)
        (@fapp0 A B (@example_unprofiled_functor A B) Z))
      (@strict_functor_compositor_lhs
        A B (@example_unprofiled_functor A B) X Y Z g f);

// An arbitrary ambient functor is not silently a Gray-hom object.
assertnot [A B : Cat]
  (F : τ (Functor A B)) ⊢
  F : τ (Obj (@GrayHom_oplax A B));
