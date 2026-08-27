/*
  Reviewer example: semantic strict-functor packages and the selected
  strict-object/lax-arrow Gray-hom profile.
*/

require open emdash.emdash3_2_gray_profiles;

// Rigid ambient negative control, deliberately outside StrictFunctor.
injective symbol example_unprofiled_functor
  (A B : Cat)
  : τ (Functor A B);

assert [A B : Cat]
  (S : τ (@StrictFunctor A B)) ⊢
  S : τ (Obj (@GrayHom_lax A B));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B))) ⊢
  Hom_cat (@GrayHom_lax A B) X Y
  ≡ @Transf_cat
      A B
      (@strict_functor A B X)
      (@strict_functor A B Y);

assert [A B : Cat]
  (X : τ (Obj (@GrayHom_lax A B))) ⊢
  @fapp0
    (@GrayHom_lax A B)
    (@Functor_cat A B)
    (@grayhom_lax_include_func A B)
    X
  ≡ @strict_functor A B X;

// Identity and composition delegate to the shared ambient transfor tower.
assert [A B : Cat]
  (X : τ (Obj (@GrayHom_lax A B))) ⊢
  @id (@GrayHom_lax A B) X
  : τ (Hom
      (@Functor_cat A B)
      (@strict_functor A B X)
      (@strict_functor A B X));

assert [A B : Cat]
  (X Y Z : τ (Obj (@GrayHom_lax A B)))
  (g : τ (Hom (@GrayHom_lax A B) Y Z))
  (f : τ (Hom (@GrayHom_lax A B) X Y)) ⊢
  @comp_fapp0 (@GrayHom_lax A B) X Y Z g f
  : τ (Hom
      (@Functor_cat A B)
      (@strict_functor A B X)
      (@strict_functor A B Z));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B))) ⊢
  @fapp1_func
    (@GrayHom_lax A B)
    (@Functor_cat A B)
    (@grayhom_lax_include_func A B)
    X Y
  ≡ @id_func
      (@Transf_cat
        A B
        (@strict_functor A B X)
        (@strict_functor A B Y));

// The next hom is the existing modification/higher-cell category.
assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B)))
  (eta theta : τ (Hom (@GrayHom_lax A B) X Y)) ⊢
  Hom_cat
    (Hom_cat (@GrayHom_lax A B) X Y)
    eta theta
  ≡ Hom_cat
      (@Transf_cat
        A B
        (@strict_functor A B X)
        (@strict_functor A B Y))
      eta theta;

assert [A : Cat] ⊢
  @strict_identity A
  : τ (Obj (@GrayHom_lax A A));

assert [A : Cat] ⊢
  @strict_identity_carrier_path A
  : τ (@=
      (Functor A A)
      (@strict_functor A A (@strict_identity A))
      (@id_func A));

// StrictFunctor is exactly the carrier/evidence Sigma package.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @strict_functor_intro A B F p
  : τ (@StrictFunctor A B);

assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @strict_functor_underlying
    A B (@strict_functor_intro A B F p)
  ≡ F;

assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @strict_functor_evidence
    A B (@strict_functor_intro A B F p)
  ≡ p;

// Constructor-visible package action computes through the ambient carrier.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  (X : τ (Obj A)) ⊢
  @fapp0 A B
    (@strict_functor A B (@strict_functor_intro A B F p)) X
  ≡ @fapp0 A B F X;

assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  [X Y : τ (Obj A)]
  (f : τ (Hom A X Y)) ⊢
  @fapp1_fapp0 A B
    (@strict_functor A B (@strict_functor_intro A B F p)) X Y f
  ≡ @fapp1_fapp0 A B F X Y f;

// For an opaque package, strictness is retained as evidence about the one
// intrinsic compositor; it is not reflected into a second or literal-id cell.
assert [A B : Cat]
  (S : τ (@StrictFunctor A B)) ⊢
  @strict_functor_evidence A B S
  : τ (@IsStrictFunctor
      A B (@strict_functor_underlying A B S));

// The retired code-specific literal-id computation does not leak to a rigid
// ambient functor.
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

// The evidence-bearing whole view is deliberately retained; only its
// constructor-visible point and hom projections compute to the carrier.
assertnot [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @strict_functor A B (@strict_functor_intro A B F p)
  ≡ F;
