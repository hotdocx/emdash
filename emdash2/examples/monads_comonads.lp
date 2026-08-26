/*
  Reviewer milestone: monad-primary triangular computation and its checked
  opposite-derived comonad.

  Whole extension retains higher action. The selected Došen runtime
  accumulation is ordinary ambient composition:

    g* o f* -> (g* o f)*.

  KleisliCut is only transparent derived notation. Opposite-derived comonad
  observations and point coextension compute into a narrow stable variance
  mirror after Op normalization; whole coextension transparently reuses the
  endpoint-swapped primary monadic whole owner. No propositional equality or
  whole proof-time bridge is involved.
*/

require open emdash.emdash3_2_monads;

// Ambient monadic beta.
assert [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A X Y))
  (g : τ (Hom A Y (@fapp0 A A T Z))) ⊢
  @comp_fapp0
    A X
    (@fapp0 A A T Y)
    (@fapp0 A A T Z)
    (@kleisli_extend_fapp0 A T M Y Z g)
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
  @comp_fapp0
    A
    (@fapp0 A A T X)
    (@fapp0 A A T Y)
    (@fapp0 A A T Z)
    (@kleisli_extend_fapp0 A T M Y Z g)
    (@kleisli_extend_fapp0 A T M X Y f)
  ≡ @kleisli_extend_fapp0
      A T M X Z
      (@comp_fapp0
        A X
        (@fapp0 A A T Y)
        (@fapp0 A A T Z)
        (@kleisli_extend_fapp0 A T M Y Z g)
        f);

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

// KleisliCut is transparent notation, not the ambient rewrite owner.
assert [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A X (@fapp0 A A T Y)))
  (g : τ (Hom A Y (@fapp0 A A T Z))) ⊢
  @kleisli_cut_fapp0 A T M X Y Z g f
  ≡ @comp_fapp0
      A X
      (@fapp0 A A T Y)
      (@fapp0 A A T Z)
      (@kleisli_extend_fapp0 A T M Y Z g)
      f;

// Ambient comonadic beta.
assert [A : Cat]
  [D : τ (Functor A A)]
  (C : τ (@Comonad A D))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A (@fapp0 A A D X) Y))
  (h : τ (Hom A Y Z)) ⊢
  @comp_fapp0
    A
    (@fapp0 A A D X)
    (@fapp0 A A D Y)
    Z
    (@tapp1_fapp0
      A A
      D (@id_func A)
      Y Z
      (@counit_comonad_transf A D C)
      h)
    (@cokleisli_extend_fapp0 A D C X Y f)
  ≡ @comp_fapp0 A (@fapp0 A A D X) Y Z h f;

// The canonical raw Op presentation enters the same stable co-beta rule.
assert [A : Cat]
  [D : τ (Functor A A)]
  (C : τ (@Comonad A D))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A (@fapp0 A A D X) Y))
  (h : τ (Hom A Y Z)) ⊢
  @comp_fapp0
    A
    (@fapp0 A A D X)
    (@fapp0 A A D Y)
    Z
    (@tapp1_fapp0
      A A D (@id_func A) Y Z
      (@Op_transf
        (Op_cat A) (Op_cat A)
        (@id_func (Op_cat A)) (@Op_func A A D)
        (@unit_monad_transf (Op_cat A) (@Op_func A A D) C))
      h)
    (@kleisli_extend_fapp0
      (Op_cat A) (@Op_func A A D) C Y X f)
  ≡ @comp_fapp0 A (@fapp0 A A D X) Y Z h f;

// Exact dual accumulation in the comonad facade.
assert [A : Cat]
  [D : τ (Functor A A)]
  (C : τ (@Comonad A D))
  (X Y Z : τ (Obj A))
  (f1 : τ (Hom A (@fapp0 A A D X) Y))
  (f2 : τ (Hom A (@fapp0 A A D Y) Z)) ⊢
  @comp_fapp0
    A
    (@fapp0 A A D X)
    (@fapp0 A A D Y)
    (@fapp0 A A D Z)
    (@cokleisli_extend_fapp0 A D C Y Z f2)
    (@cokleisli_extend_fapp0 A D C X Y f1)
  ≡ @cokleisli_extend_fapp0
      A D C X Z
      (@comp_fapp0
        A
        (@fapp0 A A D X)
        (@fapp0 A A D Y)
        Z
        f2
        (@cokleisli_extend_fapp0 A D C X Y f1));

// The primary whole owner and its transparent dual view retain another hom
// action; only the dual point projection has a separate stable runtime head.
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

assert [A : Cat]
  [D : τ (Functor A A)]
  (C : τ (@Comonad A D))
  (X Y : τ (Obj A))
  (f g : τ (Hom A (@fapp0 A A D X) Y)) ⊢
  @fapp1_func
    (Hom_cat A (@fapp0 A A D X) Y)
    (Hom_cat A (@fapp0 A A D X) (@fapp0 A A D Y))
    (@cokleisli_extend_func A D C X Y)
    f g
  : τ (Functor
      (Hom_cat (Hom_cat A (@fapp0 A A D X) Y) f g)
      (Hom_cat
        (Hom_cat A (@fapp0 A A D X) (@fapp0 A A D Y))
        (@cokleisli_extend_fapp0 A D C X Y f)
        (@cokleisli_extend_fapp0 A D C X Y g)));

// The existing adjunction constructs both exact structural instances. Its
// named unit is a proof-time usability endpoint; whole multiplication remains
// semantic and computes to the transparent G-epsilon-F construction.
assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) ⊢
  @eq_refl
    (Transf
      (@id_func R)
      (@comp_cat_fapp0 R L R G F))
    (unit_monad_transf (adjunction_monad J))
  : τ (@=
      (Transf
        (@id_func R)
        (@comp_cat_fapp0 R L R G F))
      (unit_monad_transf (adjunction_monad J))
      (unit_adj_transf J));

assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) ⊢
  mult_monad_transf (adjunction_monad J)
    ≡ adjunction_monad_mult_transf J;

assertnot [R L : Cat]
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

assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) ⊢
  comult_comonad_transf (adjunction_comonad J)
    ≡ adjunction_comonad_comult_transf J;

// Unrelated same-typed operations remain untrusted.
assertnot [A : Cat]
  [T : τ (Functor A A)]
  (M : τ (@Monad A T))
  (eta : τ (Transf (@id_func A) T)) ⊢
  unit_monad_transf M
    ≡ eta;
