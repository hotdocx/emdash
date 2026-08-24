/*
  Reviewer milestone: monad-primary triangular computation and its checked
  opposite-derived comonad.

  Whole Kleisli extension and cut retain higher action. The selected runtime
  accumulation is

    KleisliCut(g,f*) -> (KleisliCut(g,f))*

  while raw base-category composition remains generic. Co-Kleisli laws reuse
  exactly that monadic rule in the opposite category.
*/

require open emdash.emdash3_2_monads;

// Kleisli beta.
assert [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A X Y))
  (g : τ (Hom A Y (@fapp0 A A T Z))) ⊢
  @kleisli_cut_fapp0
    A T M X Y Z g
    (@tapp1_fapp0
      A A
      (@id_func A) T
      X Y
      (@unit_monad_transf A T M)
      f)
  ≡ @comp_fapp0 A X Y (@fapp0 A A T Z) g f;

// Corrected Došen-dual accumulation.
assert [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A X (@fapp0 A A T Y)))
  (g : τ (Hom A Y (@fapp0 A A T Z))) ⊢
  @kleisli_cut_fapp0
    A T M
    (@fapp0 A A T X) Y Z
    g
    (@kleisli_extend_fapp0 A T M X Y f)
  ≡ @kleisli_extend_fapp0
      A T M X Z
      (@kleisli_cut_fapp0 A T M X Y Z g f);

// Unit and multiplication observations compile into the triangular owner.
assert [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X : τ (Obj A)) ⊢
  @kleisli_extend_fapp0
    A T M X X
    (@tapp0_fapp0
      A A
      (@id_func A) T
      X
      (@unit_monad_transf A T M))
  ≡ @id A (@fapp0 A A T X);

assert [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X : τ (Obj A)) ⊢
  @tapp0_fapp0
    A A
    (@comp_cat_fapp0 A A A T T)
    T X
    (@mult_monad_transf A T M)
  ≡ @kleisli_extend_fapp0
      A T M
      (@fapp0 A A T X)
      X
      (@id A (@fapp0 A A T X));

// Raw base-category composition deliberately has no duplicate hot fold.
assertnot [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A X (@fapp0 A A T Y)))
  (g : τ (Hom A Y (@fapp0 A A T Z))) ⊢
  @comp_fapp0
    A
    (@fapp0 A A T X)
    (@fapp0 A A T Y)
    (@fapp0 A A T Z)
    (@kleisli_extend_fapp0 A T M Y Z g)
    (@kleisli_extend_fapp0 A T M X Y f)
  ≡ @kleisli_extend_fapp0
      A T M X Z
      (@kleisli_cut_fapp0 A T M X Y Z g f);

// Exact dual accumulation in the comonad facade.
assert [A : Cat]
  [D : τ (Functor A A)]
  (C : τ (@Comonad A D))
  (X Y Z : τ (Obj A))
  (f1 : τ (Hom A (@fapp0 A A D X) Y))
  (f2 : τ (Hom A (@fapp0 A A D Y) Z)) ⊢
  @cokleisli_cut_fapp0
    A D C
    X Y (@fapp0 A A D Z)
    (@cokleisli_extend_fapp0 A D C Y Z f2)
    f1
  ≡ @cokleisli_extend_fapp0
      A D C X Z
      (@cokleisli_cut_fapp0 A D C X Y Z f2 f1);

// Both whole computational owners retain another hom action.
assert [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X Y : τ (Obj A))
  (f g : τ (Hom A X (@fapp0 A A T Y))) ⊢
  @fapp1_func
    (Hom_cat A X (@fapp0 A A T Y))
    (Hom_cat A (@fapp0 A A T X) (@fapp0 A A T Y))
    (@kleisli_extend_func A T M X Y)
    f g
  : τ (Functor
      (Hom_cat (Hom_cat A X (@fapp0 A A T Y)) f g)
      (Hom_cat
        (Hom_cat A (@fapp0 A A T X) (@fapp0 A A T Y))
        (@kleisli_extend_fapp0 A T M X Y f)
        (@kleisli_extend_fapp0 A T M X Y g)));

// The existing adjunction constructs both exact structural instances.
assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) ⊢
  unit_monad_transf (adjunction_monad J)
    ≡ unit_adj_transf J;

assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) ⊢
  counit_comonad_transf (adjunction_comonad J)
    ≡ counit_adj_transf J;

// Unrelated same-typed operations remain untrusted.
assertnot [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (eta : τ (Transf (@id_func A) T)) ⊢
  unit_monad_transf M
    ≡ eta;

