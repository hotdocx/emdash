/*
  Monad-primary computation with opposite-derived comonads.

  A Monad witness is indexed by a whole endofunctor. Its unit and
  multiplication are stable full-transformation observations. Whole extension
  retains higher action, while ordinary ambient composition owns Došen's
  triangular beta and accumulation reductions.

  The primary monadic runtime orientation is

    g* o f* -> (g* o f)*

  at the generic `comp_fapp0` head. `KleisliCut(g,f)=g* o f` is retained only
  as transparent derived notation; it is not a second rewrite owner.

  A comonad on A is classified transparently as a monad on A^op. Stable
  counit/comultiplication and point coextension heads are the narrow variance
  mirror required where opposite-category normalization erases an active
  runtime discriminator. Whole coextension transparently reuses primary
  monadic whole extension. Canonical Op terms fold directly to the stable
  heads; no whole coextension unifier or propositional equality bridge is used.
  For the adjunction-induced Monad, the canonical unit remains a runtime head
  and the adjunction unit is a proof-time usability endpoint. The standard
  whole multiplication remains semantic and reduces to the transparent
  G-epsilon-F construction; its component-first triangular branch is joined
  propositionally to the whole-first semantic component.
  This module does not construct free syntax, a global commuting decision
  procedure, Kleisli or Eilenberg--Moore categories, or a TypeScript
  declaration surface.
*/

require open emdash.emdash3_2;

// Indexed relation asserting that T is a monad endofunctor on A.
injective symbol Monad
  [A : Cat]
  (T : τ (@Functor A A))
  : Grpd;

// Stable unit observation eta : id_A => T.
symbol unit_monad_transf
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  : τ (@Transf A A (@id_func A) T);

// Stable multiplication observation mu : T o T => T.
symbol mult_monad_transf
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  : τ (@Transf
      A A
      (@comp_cat_fapp0 A A A T T)
      T);

/*
  Whole Kleisli extension.

  Surface/formula:
    kleisli_extend_func(M,X,Y)[f] = f*
    f : X -> T[Y]
    f* : T[X] -> T[Y].
*/
injective symbol kleisli_extend_func
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  (X Y : τ (@Obj A))
  : τ (@Functor
      (@Hom_cat A X (@fapp0 A A T Y))
      (@Hom_cat A
        (@fapp0 A A T X)
        (@fapp0 A A T Y)));

// Stable object projection f |-> f* while the whole owner retains hom action.
symbol kleisli_extend_fapp0
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  [X Y : τ (@Obj A)]
  (f : τ (@Hom A X (@fapp0 A A T Y)))
  : τ (@Hom A
      (@fapp0 A A T X)
      (@fapp0 A A T Y));

rule @fapp0
      _ _
      (@kleisli_extend_func $A $T $M $X $Y)
      $f
  ↪ @kleisli_extend_fapp0 $A $T $M $X $Y $f;

// Semantic whole extension target: f* = mu_Y o T[f].
symbol kleisli_extend_semantic_func
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  (X Y : τ (@Obj A))
  : τ (@Functor
      (@Hom_cat A X (@fapp0 A A T Y))
      (@Hom_cat A
        (@fapp0 A A T X)
        (@fapp0 A A T Y)))
≔ @comp_cat_fapp0
    (@Hom_cat A X (@fapp0 A A T Y))
    (@Hom_cat A
      (@fapp0 A A T X)
      (@fapp0 A A T (@fapp0 A A T Y)))
    (@Hom_cat A
      (@fapp0 A A T X)
      (@fapp0 A A T Y))
    (@hom_postcomp_func
      A A
      (@id_func A)
      (@fapp0 A A T X)
      (@fapp0 A A T (@fapp0 A A T Y))
      (@fapp0 A A T Y)
      (@tapp0_fapp0
        A A
        (@comp_cat_fapp0 A A A T T)
        T Y
        (@mult_monad_transf A T M)))
    (@fapp1_func A A T X (@fapp0 A A T Y));

/*
  Proof-time semantic comparison after multiplication selects its triangular
  component normal form. Runtime keeps the stable whole/point extension heads;
  neither rule expands a hot extension redex. The point rung is registered
  directly because unification is not assumed to propagate through fapp0.
*/
unif_rule
  @kleisli_extend_func $A $T $M $X $Y
  ≡ @comp_fapp0
      Cat_cat _ _ _
      (@hom_postcomp_func
        _ _ _ _ _ _
        (@kleisli_extend_fapp0
          _ _ $M
          (@fapp0 $A $A $T $Y) $Y
          (@id $A (@fapp0 $A $A $T $Y))))
      (@fapp1_func _ _ $T $X _)
  ↪ [ tt ≡ tt ];

unif_rule
  @kleisli_extend_fapp0 $A $T $M $X $Y $f
  ≡ @hom_postcomp_fapp0
      _ _ _ _ _ _
      (@kleisli_extend_fapp0
        _ _ $M
        (@fapp0 $A $A $T $Y) $Y
        (@id $A (@fapp0 $A $A $T $Y)))
      (@fapp1_fapp0 _ _ $T $X _ $f)
  ↪ [ tt ≡ tt ];

/*
  Derived Kleisli-composition notation.

  Došen's ambient normalizer is owned by ordinary `comp_fapp0` below. The
  optional notation

    KleisliCut(g,f) = g* o f

  is the monadic dual of delta composition and is transparent rather than a
  second primitive cut owner. An explicit Kleisli category remains a separate
  construction.
*/
symbol kleisli_cut_func
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (@Obj A))
  : τ (@Functor
      (Product_cat
        (@Hom_cat A X (@fapp0 A A T Y))
        (@Hom_cat A Y (@fapp0 A A T Z)))
      (@Hom_cat A X (@fapp0 A A T Z)))
≔ @comp_cat_fapp0
    (Product_cat
      (@Hom_cat A X (@fapp0 A A T Y))
      (@Hom_cat A Y (@fapp0 A A T Z)))
    (Product_cat
      (@Hom_cat A X (@fapp0 A A T Y))
      (@Hom_cat A
        (@fapp0 A A T Y)
        (@fapp0 A A T Z)))
    (@Hom_cat A X (@fapp0 A A T Z))
    (@comp_prod_func
      A X
      (@fapp0 A A T Y)
      (@fapp0 A A T Z))
    (@Product_map_func
      (@Hom_cat A X (@fapp0 A A T Y))
      (@Hom_cat A X (@fapp0 A A T Y))
      (@Hom_cat A Y (@fapp0 A A T Z))
      (@Hom_cat A
        (@fapp0 A A T Y)
        (@fapp0 A A T Z))
      (@id_func (@Hom_cat A X (@fapp0 A A T Y)))
      (@kleisli_extend_func A T M Y Z));

// Historical semantic name retained as a transparent compatibility alias.
symbol kleisli_cut_semantic_func
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (@Obj A))
  : τ (@Functor
      (Product_cat
        (@Hom_cat A X (@fapp0 A A T Y))
        (@Hom_cat A Y (@fapp0 A A T Z)))
      (@Hom_cat A X (@fapp0 A A T Z)))
≔ @kleisli_cut_func A T M X Y Z;

// Transparent point notation: KleisliCut(g,f) = g* o f.
symbol kleisli_cut_fapp0
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  [X Y Z : τ (@Obj A)]
  (g : τ (@Hom A Y (@fapp0 A A T Z)))
  (f : τ (@Hom A X (@fapp0 A A T Y)))
  : τ (@Hom A X (@fapp0 A A T Z))
≔ @comp_fapp0
    A X
    (@fapp0 A A T Y)
    (@fapp0 A A T Z)
    (@kleisli_extend_fapp0 A T M Y Z g)
    f;

symbol kleisli_cut_semantic_path
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (@Obj A))
  : τ (@=
      (Functor
        (Product_cat
          (@Hom_cat A X (@fapp0 A A T Y))
          (@Hom_cat A Y (@fapp0 A A T Z)))
        (@Hom_cat A X (@fapp0 A A T Z)))
      (@kleisli_cut_func A T M X Y Z)
      (@kleisli_cut_semantic_func A T M X Y Z))
≔ @eq_refl
    (Functor
      (Product_cat
        (@Hom_cat A X (@fapp0 A A T Y))
        (@Hom_cat A Y (@fapp0 A A T Z)))
      (@Hom_cat A X (@fapp0 A A T Z)))
    (@kleisli_cut_func A T M X Y Z);

symbol kleisli_cut_fapp0_path
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  [X Y Z : τ (@Obj A)]
  (g : τ (@Hom A Y (@fapp0 A A T Z)))
  (f : τ (@Hom A X (@fapp0 A A T Y)))
  : τ (@=
      (Hom A X (@fapp0 A A T Z))
      (@kleisli_cut_fapp0 A T M X Y Z g f)
      (@comp_fapp0
        A X
        (@fapp0 A A T Y)
        (@fapp0 A A T Z)
        (@kleisli_extend_fapp0 A T M Y Z g)
        f))
≔ @eq_refl
    (Hom A X (@fapp0 A A T Z))
    (@kleisli_cut_fapp0 A T M X Y Z g f);

// Every extension arrow in Terminal_cat has the terminal arrow normal form.
// This narrow projection joins ambient accumulation with Terminal composition.
rule @kleisli_extend_fapp0
      Terminal_cat _ _ _ _ _
  ↪ Terminal_obj;

// Ambient Došen beta: g* o eta^c(f) -> g o f.
rule @comp_fapp0
      _
      _ _ _
      (@kleisli_extend_fapp0 $A $T $M $Y $Z $g)
      (@tapp1_fapp0
        _ _
        _ _
        $X $Y
        (@unit_monad_transf _ _ $M)
        $f)
  ↪ @comp_fapp0 $A $X $Y (@fapp0 $A $A $T $Z) $g $f;

// Component-first beta bridge at f=id_X. Keep ambient composition visible so
// specialized categories select their own identity-composition normal form.
rule @comp_fapp0
      _
      _ _ _
      (@kleisli_extend_fapp0 $A $T $M $X $Z $g)
      (@tapp0_fapp0
        _ _
        _ _
        $X
        (@unit_monad_transf _ _ $M))
  ↪ @comp_fapp0
      $A $X $X
      (@fapp0 $A $A $T $Z)
      $g
      (@id $A $X);

// Exact ambient Došen direction: g* o f* -> (g* o f)*.
rule @comp_fapp0
      _
      _ _ _
      (@kleisli_extend_fapp0 $A $T $M $Y $Z $g)
      (@kleisli_extend_fapp0 _ _ $M $X $Y $f)
  ↪ @kleisli_extend_fapp0
      $A $T $M $X $Z
      (@comp_fapp0
        $A
        $X
        (@fapp0 $A $A $T $Y)
        (@fapp0 $A $A $T $Z)
        (@kleisli_extend_fapp0 $A $T $M $Y $Z $g)
        $f);

// Typed equality view of the ambient accumulation conversion.
symbol kleisli_extend_comp_path
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  [X Y Z : τ (@Obj A)]
  (g : τ (@Hom A Y (@fapp0 A A T Z)))
  (f : τ (@Hom A X (@fapp0 A A T Y)))
  : τ (@=
      (Hom A (@fapp0 A A T X) (@fapp0 A A T Z))
      (@comp_fapp0
        A
        (@fapp0 A A T X)
        (@fapp0 A A T Y)
        (@fapp0 A A T Z)
        (@kleisli_extend_fapp0 A T M Y Z g)
        (@kleisli_extend_fapp0 A T M X Y f))
      (@kleisli_extend_fapp0
        A T M X Z
        (@comp_fapp0
          A X
          (@fapp0 A A T Y)
          (@fapp0 A A T Z)
          (@kleisli_extend_fapp0 A T M Y Z g)
          f)))
≔ @eq_refl
    (Hom A (@fapp0 A A T X) (@fapp0 A A T Z))
    (@kleisli_extend_fapp0
      A T M X Z
      (@comp_fapp0
        A X
        (@fapp0 A A T Y)
        (@fapp0 A A T Z)
        (@kleisli_extend_fapp0 A T M Y Z g)
        f));

// (eta_X)* -> id_TX at the canonical unit component.
rule @kleisli_extend_fapp0
      $A $T $M $X $X
      (@tapp0_fapp0
        _ _
        _ _
        $X
        (@unit_monad_transf _ _ $M))
  ↪ @id $A (@fapp0 $A $A $T $X);

// Standard multiplication components compile into the triangular owner:
//   mu_X -> (id_TX)*.
rule @tapp0_fapp0
      _ _
      _ _
      $X
      (@mult_monad_transf $A $T $M)
  ↪ @kleisli_extend_fapp0
      $A $T $M
      (@fapp0 $A $A $T $X)
      $X
      (@id $A (@fapp0 $A $A $T $X));

// --------------------------------------------------------------------------
// Opposite-derived comonads
// --------------------------------------------------------------------------

// A comonad on A is transparently a monad on A^op.
symbol Comonad
  [A : Cat]
  (D : τ (@Functor A A))
  : Grpd
≔ @Monad
    (Op_cat A)
    (@Op_func A A D);

// Readability views of the involutive evidence transport.
symbol Op_monad
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  : τ (@Comonad
      (Op_cat A)
      (@Op_func A A T))
≔ M;

symbol Op_comonad
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  : τ (@Monad
      (Op_cat A)
      (@Op_func A A D))
≔ C;

// Stable standard counit observation. This is the canonical whole dual owner
// after Op normalization has erased the original category discriminator.
symbol counit_comonad_transf
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  : τ (@Transf A A D (@id_func A));

// Stable standard comultiplication observation.
symbol comult_comonad_transf
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  : τ (@Transf
      A A
      D
      (@comp_cat_fapp0 A A A D D));

/*
  Whole observation duality is computational in both directions. The outer
  Op_transf is the discriminator, so these generic rules do not rewrite an
  unwrapped primary Monad operation. The reverse pair supplies double-opposite
  recovery for a stable comonad observation.
*/
rule @Op_transf
      _ _ _ _
      (@unit_monad_transf $A $T $M)
  ↪ @counit_comonad_transf
      (Op_cat $A) (@Op_func $A $A $T) $M;

rule @Op_transf
      _ _ _ _
      (@mult_monad_transf $A $T $M)
  ↪ @comult_comonad_transf
      (Op_cat $A) (@Op_func $A $A $T) $M;

rule @Op_transf
      _ _ _ _
      (@counit_comonad_transf $A $D $C)
  ↪ @unit_monad_transf
      (Op_cat $A) (@Op_func $A $A $D) $C;

rule @Op_transf
      _ _ _ _
      (@comult_comonad_transf $A $D $C)
  ↪ @mult_monad_transf
      (Op_cat $A) (@Op_func $A $A $D) $C;

// Computational counit component, directly reusing the dual unit component.
symbol counit_comonad_fapp0
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X : τ (@Obj A))
  : τ (@Hom A (@fapp0 A A D X) X)
≔ @tapp0_fapp0
    (Op_cat A)
    (Op_cat A)
    (@id_func (Op_cat A))
    (@Op_func A A D)
    X
    (@unit_monad_transf
      (Op_cat A)
      (@Op_func A A D)
      C);

// Computational comultiplication component from the dual multiplication.
symbol comult_comonad_fapp0
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X : τ (@Obj A))
  : τ (@Hom A
      (@fapp0 A A D X)
      (@fapp0 A A D (@fapp0 A A D X)))
≔ @tapp0_fapp0
    (Op_cat A)
    (Op_cat A)
    (@comp_cat_fapp0
      (Op_cat A)
      (Op_cat A)
      (Op_cat A)
      (@Op_func A A D)
      (@Op_func A A D))
    (@Op_func A A D)
    X
    (@mult_monad_transf
      (Op_cat A)
      (@Op_func A A D)
      C);

// Direct opposite unit/multiplication components fold toward the stable
// comonad components. This direction preserves the component-first triangular
// discriminators and joins component projection after the whole Op fold.
rule @tapp0_fapp0
      _ _ _ _
      $X
      (@unit_monad_transf _ (@Op_func $A $A $D) $C)
  ↪ @tapp0_fapp0
      $A $A
      $D (@id_func $A)
      $X
      (@counit_comonad_transf $A $D $C);

rule @tapp0_fapp0
      _ _ _ _
      $X
      (@mult_monad_transf _ (@Op_func $A $A $D) $C)
  ↪ @tapp0_fapp0
      $A $A
      $D (@comp_cat_fapp0 $A $A $A $D $D)
      $X
      (@comult_comonad_transf $A $D $C);

// Antecedental counit action. The whole stable observation remains available,
// and its canonical Op fold supplies the underlying dual-unit interpretation.
symbol counit_comonad_antecedent_func
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X Y : τ (@Obj A))
  : τ (@Functor
      (@Hom_cat A X Y)
      (@Hom_cat A (@fapp0 A A D X) Y))
≔ @tapp1_func
    A A
    D (@id_func A)
    X Y
    (@counit_comonad_transf A D C);

/*
  Whole coextension is transparently endpoint-swapped monadic extension in
  A^op. No triangular rule discriminates on this whole head, so a second stable
  whole owner and proof-time comparison are unnecessary. The primary monadic
  whole owner retains higher action; its generic object projection reaches the
  stable point fold below.
*/
symbol cokleisli_extend_func
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X Y : τ (@Obj A))
  : τ (@Functor
      (@Hom_cat A (@fapp0 A A D X) Y)
      (@Hom_cat A (@fapp0 A A D X) (@fapp0 A A D Y)))
≔ @kleisli_extend_func
    (Op_cat A)
    (@Op_func A A D)
    C
    Y X;

// Stable point coextension is the runtime discriminator used by ambient
// comonad beta, accumulation, counit identity, and comultiplication rules.
symbol cokleisli_extend_fapp0
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  [X Y : τ (@Obj A)]
  (f : τ (@Hom A (@fapp0 A A D X) Y))
  : τ (@Hom A (@fapp0 A A D X) (@fapp0 A A D Y));

// Historical comparison names remain transparent aliases of the selected
// whole and point surfaces; they introduce no second semantic body.
symbol cokleisli_extend_op_func
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X Y : τ (@Obj A))
  : τ (@Functor
      (@Hom_cat A (@fapp0 A A D X) Y)
      (@Hom_cat A (@fapp0 A A D X) (@fapp0 A A D Y)))
≔ @cokleisli_extend_func A D C X Y;

symbol cokleisli_extend_op_fapp0
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  [X Y : τ (@Obj A)]
  (f : τ (@Hom A (@fapp0 A A D X) Y))
  : τ (@Hom A (@fapp0 A A D X) (@fapp0 A A D Y))
≔ @cokleisli_extend_fapp0 A D C X Y f;

/*
  The point fold is runtime because ambient co-beta and accumulation need the
  stable dual discriminator after Op_cat has normalized away. Matching only
  Op_func(D) avoids repeated reducible category and endpoint guards.
*/
rule @kleisli_extend_fapp0
      _ (@Op_func $A $A $D) $C $Y $X $f
  ↪ @cokleisli_extend_fapp0 $A $D $C $X $Y $f;

// Terminal coextension uses the ambient terminal-arrow normal form.
rule @cokleisli_extend_fapp0
      Terminal_cat _ _ _ _ _
  ↪ Terminal_obj;

// Ambient Došen co-beta: epsilon^a(f2) o Delta(f1) -> f2 o f1.
rule @comp_fapp0
      _
      _ _ _
      (@tapp1_fapp0
        _ _
        _ _
        $Y $Z
        (@counit_comonad_transf $A $D $C)
        $f2)
      (@cokleisli_extend_fapp0 _ _ $C $X $Y $f1)
  ↪ @comp_fapp0
      $A
      (@fapp0 $A $A $D $X)
      $Y $Z
      $f2 $f1;

// Component-first co-beta bridge at f2=id_Y.
rule @comp_fapp0
      _
      _ _ _
      (@tapp0_fapp0
        _ _
        _ _
        $Y
        (@counit_comonad_transf $A $D $C))
      (@cokleisli_extend_fapp0 _ _ $C $X $Y $f1)
  ↪ @comp_fapp0
      $A
      (@fapp0 $A $A $D $X)
      $Y $Y
      (@id $A $Y)
      $f1;

// Exact ambient Došen accumulation:
//   Delta(f2) o Delta(f1) -> Delta(f2 o Delta(f1)).
rule @comp_fapp0
      _
      _ _ _
      (@cokleisli_extend_fapp0 $A $D $C $Y $Z $f2)
      (@cokleisli_extend_fapp0 _ _ $C $X $Y $f1)
  ↪ @cokleisli_extend_fapp0
      $A $D $C $X $Z
      (@comp_fapp0
        $A
        (@fapp0 $A $A $D $X)
        (@fapp0 $A $A $D $Y)
        $Z
        $f2
        (@cokleisli_extend_fapp0 $A $D $C $X $Y $f1));

// Coextension of the standard counit component is identity.
rule @cokleisli_extend_fapp0
      $A $D $C $X $X
      (@tapp0_fapp0
        _ _
        _ _
        $X
        (@counit_comonad_transf _ _ $C))
  ↪ @id $A (@fapp0 $A $A $D $X);

// Standard comultiplication components compile into coextension of identity:
//   delta_X -> Delta(id_DX).
rule @tapp0_fapp0
      _ _
      _ _
      $X
      (@comult_comonad_transf $A $D $C)
  ↪ @cokleisli_extend_fapp0
      $A $D $C
      $X
      (@fapp0 $A $A $D $X)
      (@id $A (@fapp0 $A $A $D $X));

// Whole derived co-Kleisli composition; input order is (f2,f1).
symbol cokleisli_cut_func
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X Y Z : τ (@Obj A))
  : τ (@Functor
      (Product_cat
        (@Hom_cat A (@fapp0 A A D Y) Z)
        (@Hom_cat A (@fapp0 A A D X) Y))
      (@Hom_cat A (@fapp0 A A D X) Z))
≔ @comp_cat_fapp0
    (Product_cat
      (@Hom_cat A (@fapp0 A A D Y) Z)
      (@Hom_cat A (@fapp0 A A D X) Y))
    (Product_cat
      (@Hom_cat A (@fapp0 A A D X) (@fapp0 A A D Y))
      (@Hom_cat A (@fapp0 A A D Y) Z))
    (@Hom_cat A (@fapp0 A A D X) Z)
    (@comp_prod_func
      A
      (@fapp0 A A D X)
      (@fapp0 A A D Y)
      Z)
    (@comp_cat_fapp0
      (Product_cat
        (@Hom_cat A (@fapp0 A A D Y) Z)
        (@Hom_cat A (@fapp0 A A D X) Y))
      (Product_cat
        (@Hom_cat A (@fapp0 A A D X) Y)
        (@Hom_cat A (@fapp0 A A D Y) Z))
      (Product_cat
        (@Hom_cat A (@fapp0 A A D X) (@fapp0 A A D Y))
        (@Hom_cat A (@fapp0 A A D Y) Z))
      (@Product_map_func
        (@Hom_cat A (@fapp0 A A D X) Y)
        (@Hom_cat A (@fapp0 A A D X) (@fapp0 A A D Y))
        (@Hom_cat A (@fapp0 A A D Y) Z)
        (@Hom_cat A (@fapp0 A A D Y) Z)
        (@cokleisli_extend_func A D C X Y)
        (@id_func (@Hom_cat A (@fapp0 A A D Y) Z)))
      (@Product_swap_func
        (@Hom_cat A (@fapp0 A A D Y) Z)
        (@Hom_cat A (@fapp0 A A D X) Y)));

// CoKleisliCut(f2,f1) = f2 o Delta(f1).
symbol cokleisli_cut_fapp0
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  [X Y Z : τ (@Obj A)]
  (f2 : τ (@Hom A (@fapp0 A A D Y) Z))
  (f1 : τ (@Hom A (@fapp0 A A D X) Y))
  : τ (@Hom A (@fapp0 A A D X) Z)
≔ @comp_fapp0
    A
    (@fapp0 A A D X)
    (@fapp0 A A D Y)
    Z
    f2
    (@cokleisli_extend_fapp0 A D C X Y f1);

// --------------------------------------------------------------------------
// Monad and comonad induced by an existing adjunction
// --------------------------------------------------------------------------

/*
  Multiplication of the adjunction monad:

    G epsilon F : (G F)(G F) => G F.

  The inner whole action precomposes the counit by F; the outer whole action
  postcomposes the resulting transformation by G.
*/
symbol adjunction_monad_mult_transf
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@Transf
      R R
      (@comp_cat_fapp0
        R R R
        (@comp_cat_fapp0 R L R G F)
        (@comp_cat_fapp0 R L R G F))
      (@comp_cat_fapp0 R L R G F))
≔ @fapp0
    (@Transf_cat
      R L
      (@comp_cat_fapp0
        R L L
        (@comp_cat_fapp0 L R L F G)
        F)
      (@comp_cat_fapp0 R L L (@id_func L) F))
    (@Transf_cat
      R R
      (@comp_cat_fapp0
        R L R
        G
        (@comp_cat_fapp0
          R L L
          (@comp_cat_fapp0 L R L F G)
          F))
      (@comp_cat_fapp0
        R L R
        G
        (@comp_cat_fapp0 R L L (@id_func L) F)))
    (@comp_cat_cov_fapp1_func
      R L R
      G
      (@comp_cat_fapp0
        R L L
        (@comp_cat_fapp0 L R L F G)
        F)
      (@comp_cat_fapp0 R L L (@id_func L) F))
    (@fapp0
      (@Transf_cat
        L L
        (@comp_cat_fapp0 L R L F G)
        (@id_func L))
      (@Transf_cat
        R L
        (@comp_cat_fapp0
          R L L
          (@comp_cat_fapp0 L R L F G)
          F)
        (@comp_cat_fapp0 R L L (@id_func L) F))
      (@comp_cat_con_fapp1_func
        R L L
        F
        (@comp_cat_fapp0 L R L F G)
        (@id_func L))
      (@counit_adj_transf R L F G J));

// Selected monad of an adjunction, on the source R of the left adjoint.
injective symbol adjunction_monad
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@Monad
      R
      (@comp_cat_fapp0 R L R G F));

/*
  Declaration-backed unit usability agreement for the adjunction-induced
  Monad.

  The canonical Monad unit remains the runtime discriminator for the
  triangular calculus. The adjunction unit is a proof-time comparison
  endpoint, as in the established adjunction-usability boundary. Standard
  multiplication is not a triangular discriminator at the whole level, so it
  retains the semantic runtime projection to G-epsilon-F below.
*/
unif_rule
  @unit_monad_transf
    _ _
    (@adjunction_monad _ _ _ _ $J)
  ≡ @unit_adj_transf _ _ _ _ $J
  ↪ [ tt ≡ tt ];

/*
  First leg of the multiplication-component projection diamond.

  This declaration deliberately precedes the whole semantic multiplication
  projection below. At this point the generic component rule checks the common
  ancestor against `(id_TX)*` by reflexivity. After the whole projection is
  installed, the path's source also presents the G-epsilon-F component.
*/
symbol adjunction_monad_mult_component_to_extension_path
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  (X : τ (@Obj R))
  : τ (@=
      (Hom R
        (@fapp0
          R R
          (@comp_cat_fapp0
            R R R
            (@comp_cat_fapp0 R L R G F)
            (@comp_cat_fapp0 R L R G F))
          X)
        (@fapp0 R R (@comp_cat_fapp0 R L R G F) X))
      (@tapp0_fapp0
        R R
        (@comp_cat_fapp0
          R R R
          (@comp_cat_fapp0 R L R G F)
          (@comp_cat_fapp0 R L R G F))
        (@comp_cat_fapp0 R L R G F)
        X
        (@mult_monad_transf
          R
          (@comp_cat_fapp0 R L R G F)
          (@adjunction_monad R L F G J)))
      (@kleisli_extend_fapp0
        R
        (@comp_cat_fapp0 R L R G F)
        (@adjunction_monad R L F G J)
        (@fapp0 R R (@comp_cat_fapp0 R L R G F) X)
        X
        (@id R (@fapp0 R R (@comp_cat_fapp0 R L R G F) X))))
≔ @eq_refl
    (Hom R
      (@fapp0
        R R
        (@comp_cat_fapp0
          R R R
          (@comp_cat_fapp0 R L R G F)
          (@comp_cat_fapp0 R L R G F))
        X)
      (@fapp0 R R (@comp_cat_fapp0 R L R G F) X))
    (@tapp0_fapp0
      R R
      (@comp_cat_fapp0
        R R R
        (@comp_cat_fapp0 R L R G F)
        (@comp_cat_fapp0 R L R G F))
      (@comp_cat_fapp0 R L R G F)
      X
      (@mult_monad_transf
        R
        (@comp_cat_fapp0 R L R G F)
        (@adjunction_monad R L F G J)));

rule @mult_monad_transf
      $R _
      (@adjunction_monad $R $L $F $G $J)
  ↪ @adjunction_monad_mult_transf $R $L $F $G $J;

// Propositional join of the whole-first G-epsilon-F component and the
// component-first triangular extension normal form.
symbol adjunction_monad_mult_component_path
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  (X : τ (@Obj R))
  : τ (@=
      (Hom R
        (@fapp0
          R R
          (@comp_cat_fapp0
            R R R
            (@comp_cat_fapp0 R L R G F)
            (@comp_cat_fapp0 R L R G F))
          X)
        (@fapp0 R R (@comp_cat_fapp0 R L R G F) X))
      (@tapp0_fapp0
        R R
        (@comp_cat_fapp0
          R R R
          (@comp_cat_fapp0 R L R G F)
          (@comp_cat_fapp0 R L R G F))
        (@comp_cat_fapp0 R L R G F)
        X
        (@adjunction_monad_mult_transf R L F G J))
      (@kleisli_extend_fapp0
        R
        (@comp_cat_fapp0 R L R G F)
        (@adjunction_monad R L F G J)
        (@fapp0 R R (@comp_cat_fapp0 R L R G F) X)
        X
        (@id R (@fapp0 R R (@comp_cat_fapp0 R L R G F) X))))
≔ @adjunction_monad_mult_component_to_extension_path R L F G J X;

/*
  Comultiplication of the adjunction comonad.

  This is definitionally the opposite of the concrete multiplication of the
  monad induced by Op_adjunction(J). Mathematically it is the usual

    F eta G : F G => (F G)(F G).

  Selecting the Op-derived term here makes the transparent construction and
  the stable witness share one runtime normal form.
*/
symbol adjunction_comonad_comult_transf
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@Transf
      L L
      (@comp_cat_fapp0 L R L F G)
      (@comp_cat_fapp0
        L L L
        (@comp_cat_fapp0 L R L F G)
        (@comp_cat_fapp0 L R L F G)))
≔ @Op_transf
    (Op_cat L) (Op_cat L)
    (@comp_cat_fapp0
      (Op_cat L) (Op_cat L) (Op_cat L)
      (@Op_func L L (@comp_cat_fapp0 L R L F G))
      (@Op_func L L (@comp_cat_fapp0 L R L F G)))
    (@Op_func L L (@comp_cat_fapp0 L R L F G))
    (@adjunction_monad_mult_transf
      (Op_cat L) (Op_cat R)
      (@Op_func L R G) (@Op_func R L F)
      (@Op_adjunction R L F G J));

// Selected comonad of an adjunction, on the target L of the left adjoint.
// This is the narrow stable witness mirror: the transparent opposite-
// adjunction construction folds into it before operation projection.
injective symbol adjunction_comonad
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@Comonad
      L
      (@comp_cat_fapp0 L R L F G));

// The monad of the opposite adjunction selects the same stable witness.
rule @adjunction_monad
      _ _ _ _
      (@Op_adjunction $R $L $F $G $J)
  ↪ @adjunction_comonad $R $L $F $G $J;

// Underlying Monad-on-opposite observations compute to the dual operations.
rule @unit_monad_transf
      _ _
      (@adjunction_comonad $R $L $F $G $J)
  ↪ @Op_transf
      $L $L
      (@comp_cat_fapp0 $L $R $L $F $G)
      (@id_func $L)
      (@counit_adj_transf $R $L $F $G $J);

rule @mult_monad_transf
      _ _
      (@adjunction_comonad $R $L $F $G $J)
  ↪ @Op_transf
      $L $L
      (@comp_cat_fapp0 $L $R $L $F $G)
      (@comp_cat_fapp0
        $L $L $L
        (@comp_cat_fapp0 $L $R $L $F $G)
        (@comp_cat_fapp0 $L $R $L $F $G))
      (@adjunction_comonad_comult_transf $R $L $F $G $J);

// Stable standard observations compute directly for the concrete instance.
rule @counit_comonad_transf
      _ _
      (@adjunction_comonad $R $L $F $G $J)
  ↪ @counit_adj_transf $R $L $F $G $J;

rule @comult_comonad_transf
      _ _
      (@adjunction_comonad $R $L $F $G $J)
  ↪ @adjunction_comonad_comult_transf $R $L $F $G $J;
