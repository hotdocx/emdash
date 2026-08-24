/*
  Monad-primary computation with opposite-derived comonads.

  A Monad witness is indexed by a whole endofunctor. Its unit and
  multiplication are stable full-transformation observations. Whole Kleisli
  extension and whole Kleisli cut retain higher action, while their capped
  projections own the Došen-style triangular computation.

  Raw categorical composition remains at the generic `comp_fapp0` owner. In
  particular this module does not add a broad

    g* o f* -> (g* o f)*

  rule to arbitrary base-category composition: that spelling conflicts with
  existing opposite and specialized-category computation. The selected hot
  form is instead

    KleisliCut(g,f*) -> (KleisliCut(g,f))*.

  A comonad on A is transparently a monad on A^op. Co-Kleisli extension and
  cut are endpoint-swapped views of the same whole owners, so the dual
  computations introduce no second runtime law family. This module does not
  construct free syntax, a global commuting decision procedure, Kleisli or
  Eilenberg--Moore categories, or a TypeScript declaration surface.
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

// The stable whole owner agrees propositionally with mu_Y o T[-].
constant symbol kleisli_extend_semantic_path
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  (X Y : τ (@Obj A))
  : τ (@=
      (Functor
        (@Hom_cat A X (@fapp0 A A T Y))
        (@Hom_cat A (@fapp0 A A T X) (@fapp0 A A T Y)))
      (@kleisli_extend_func A T M X Y)
      (@kleisli_extend_semantic_func A T M X Y));

/*
  Whole Kleisli cut.

  The input order is (f,g), represented by Product_pair(f,g), and the point
  observation is named with composition order (g,f):

    KleisliCut(g,f) = g* o f.
*/
injective symbol kleisli_cut_func
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  (X Y Z : τ (@Obj A))
  : τ (@Functor
      (Product_cat
        (@Hom_cat A X (@fapp0 A A T Y))
        (@Hom_cat A Y (@fapp0 A A T Z)))
      (@Hom_cat A X (@fapp0 A A T Z)));

// Stable capped Kleisli cut: g* o f.
symbol kleisli_cut_fapp0
  [A : Cat]
  [T : τ (@Functor A A)]
  (M : τ (@Monad A T))
  [X Y Z : τ (@Obj A)]
  (g : τ (@Hom A Y (@fapp0 A A T Z)))
  (f : τ (@Hom A X (@fapp0 A A T Y)))
  : τ (@Hom A X (@fapp0 A A T Z));

rule @fapp0
      _ _
      (@kleisli_cut_func $A $T $M $X $Y $Z)
      $fg
  ↪ @kleisli_cut_fapp0
      $A $T $M $X $Y $Z
      (sigma_Snd $fg)
      (sigma_Fst $fg);

// Whole semantic cut target: map (f,g) to (f,g*) and compose.
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

// Whole and pointwise semantic comparisons remain equality evidence.
constant symbol kleisli_cut_semantic_path
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
      (@kleisli_cut_semantic_func A T M X Y Z));

constant symbol kleisli_cut_fapp0_path
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
        f));

// Kleisli beta: KleisliCut(g,eta^c(f)) -> g o f.
rule @kleisli_cut_fapp0
      $A $T $M
      $X $Y $Z
      $g
      (@tapp1_fapp0
        $A $A
        _ $T
        $X $Y
        (@unit_monad_transf $A $T $M)
        $f)
  ↪ @comp_fapp0 $A $X $Y (@fapp0 $A $A $T $Z) $g $f;

// Component-first beta overlap at f = id_X.
rule @kleisli_cut_fapp0
      $A $T $M
      $X $X _
      $g
      (@tapp0_fapp0
        $A $A
        _ $T
        $X
        (@unit_monad_transf $A $T $M))
  ↪ $g;

// Correct Došen direction at the selected stable cut owner:
//   KleisliCut(g,f*) -> (KleisliCut(g,f))*.
rule @kleisli_cut_fapp0
      $A $T $M
      _ $Y $Z
      $g
      (@kleisli_extend_fapp0 $A $T $M $X $Y $f)
  ↪ @kleisli_extend_fapp0
      $A $T $M $X $Z
      (@kleisli_cut_fapp0 $A $T $M $X $Y $Z $g $f);

// The familiar raw equation is retained propositionally in its normalization
// direction, without making raw base composition another runtime owner:
//   g* o f* = (KleisliCut(g,f))*.
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
        (@kleisli_cut_fapp0 A T M X Y Z g f)))
≔ @eq_sym
    (Hom A (@fapp0 A A T X) (@fapp0 A A T Z))
    (@kleisli_extend_fapp0
      A T M X Z
      (@kleisli_cut_fapp0 A T M X Y Z g f))
    (@comp_fapp0
      A
      (@fapp0 A A T X)
      (@fapp0 A A T Y)
      (@fapp0 A A T Z)
      (@kleisli_extend_fapp0 A T M Y Z g)
      (@kleisli_extend_fapp0 A T M X Y f))
    (@kleisli_cut_fapp0_path
      A T M
      (@fapp0 A A T X) Y Z
      g
      (@kleisli_extend_fapp0 A T M X Y f));

// (eta_X)* -> id_TX at the canonical unit component.
rule @kleisli_extend_fapp0
      $A $T $M $X $X
      (@tapp0_fapp0
        $A $A
        _ $T
        $X
        (@unit_monad_transf $A $T $M))
  ↪ @id $A (@fapp0 $A $A $T $X);

// Standard multiplication components compile into the triangular owner:
//   mu_X -> (id_TX)*.
rule @tapp0_fapp0
      $A $A
      _ $T
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

// Stable standard counit observation.
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

// The stable whole observations agree propositionally with opposite
// unit/multiplication. They do not unfold at runtime, avoiding double-Op
// projection-order competition in concrete instances.
constant symbol counit_comonad_op_path
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  : τ (@=
      (Transf D (@id_func A))
      (@counit_comonad_transf A D C)
      (@Op_transf
        (Op_cat A)
        (Op_cat A)
        (@id_func (Op_cat A))
        (@Op_func A A D)
        (@unit_monad_transf
          (Op_cat A)
          (@Op_func A A D)
          C)));

constant symbol comult_comonad_op_path
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  : τ (@=
      (Transf D (@comp_cat_fapp0 A A A D D))
      (@comult_comonad_transf A D C)
      (@Op_transf
        (Op_cat A)
        (Op_cat A)
        (@comp_cat_fapp0
          (Op_cat A)
          (Op_cat A)
          (Op_cat A)
          (@Op_func A A D)
          (@Op_func A A D))
        (@Op_func A A D)
        (@mult_monad_transf
          (Op_cat A)
          (@Op_func A A D)
          C)));

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

// Whole-observation component agreements are theorem-level.
constant symbol counit_comonad_fapp0_path
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X : τ (@Obj A))
  : τ (@=
      (Hom A (@fapp0 A A D X) X)
      (@tapp0_fapp0
        A A
        D (@id_func A)
        X
        (@counit_comonad_transf A D C))
      (@counit_comonad_fapp0 A D C X));

constant symbol comult_comonad_fapp0_path
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X : τ (@Obj A))
  : τ (@=
      (Hom A
        (@fapp0 A A D X)
        (@fapp0 A A D (@fapp0 A A D X)))
      (@tapp0_fapp0
        A A
        D (@comp_cat_fapp0 A A A D D)
        X
        (@comult_comonad_transf A D C))
      (@comult_comonad_fapp0 A D C X));

// Antecedental counit action, expressed directly through the dual unit owner.
symbol counit_comonad_antecedent_func
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X Y : τ (@Obj A))
  : τ (@Functor
      (@Hom_cat A X Y)
      (@Hom_cat A (@fapp0 A A D X) Y))
≔ @tapp1_func
    (Op_cat A)
    (Op_cat A)
    (@id_func (Op_cat A))
    (@Op_func A A D)
    Y X
    (@unit_monad_transf
      (Op_cat A)
      (@Op_func A A D)
      C);

// The computational antecedental action agrees with the standard counit.
constant symbol counit_comonad_antecedent_path
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  (X Y : τ (@Obj A))
  : τ (@=
      (Functor
        (@Hom_cat A X Y)
        (@Hom_cat A (@fapp0 A A D X) Y))
      (@tapp1_func
        A A
        D (@id_func A)
        X Y
        (@counit_comonad_transf A D C))
      (@counit_comonad_antecedent_func A D C X Y));

// Delta(f) is the endpoint-swapped Kleisli extension in A^op.
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

symbol cokleisli_extend_fapp0
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  [X Y : τ (@Obj A)]
  (f : τ (@Hom A (@fapp0 A A D X) Y))
  : τ (@Hom A (@fapp0 A A D X) (@fapp0 A A D Y))
≔ @kleisli_extend_fapp0
    (Op_cat A)
    (@Op_func A A D)
    C
    Y X
    f;

// Whole co-Kleisli cut; its product input order is (f2,f1).
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
≔ @kleisli_cut_func
    (Op_cat A)
    (@Op_func A A D)
    C
    Z Y X;

// CoKleisliCut(f2,f1) = f2 o Delta(f1).
symbol cokleisli_cut_fapp0
  [A : Cat]
  [D : τ (@Functor A A)]
  (C : τ (@Comonad A D))
  [X Y Z : τ (@Obj A)]
  (f2 : τ (@Hom A (@fapp0 A A D Y) Z))
  (f1 : τ (@Hom A (@fapp0 A A D X) Y))
  : τ (@Hom A (@fapp0 A A D X) Z)
≔ @kleisli_cut_fapp0
    (Op_cat A)
    (@Op_func A A D)
    C
    Z Y X
    f1 f2;

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

rule @unit_monad_transf
      $R _
      (@adjunction_monad $R $L $F $G $J)
  ↪ @unit_adj_transf $R $L $F $G $J;

rule @mult_monad_transf
      $R _
      (@adjunction_monad $R $L $F $G $J)
  ↪ @adjunction_monad_mult_transf $R $L $F $G $J;

/*
  Comultiplication of the adjunction comonad:

    F eta G : F G => (F G)(F G).

  The inner whole action precomposes the unit by G; the outer whole action
  postcomposes the resulting transformation by F.
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
≔ @fapp0
    (@Transf_cat
      L R
      (@comp_cat_fapp0 L R R (@id_func R) G)
      (@comp_cat_fapp0
        L R R
        (@comp_cat_fapp0 R L R G F)
        G))
    (@Transf_cat
      L L
      (@comp_cat_fapp0
        L R L
        F
        (@comp_cat_fapp0 L R R (@id_func R) G))
      (@comp_cat_fapp0
        L R L
        F
        (@comp_cat_fapp0
          L R R
          (@comp_cat_fapp0 R L R G F)
          G)))
    (@comp_cat_cov_fapp1_func
      L R L
      F
      (@comp_cat_fapp0 L R R (@id_func R) G)
      (@comp_cat_fapp0
        L R R
        (@comp_cat_fapp0 R L R G F)
        G))
    (@fapp0
      (@Transf_cat
        R R
        (@id_func R)
        (@comp_cat_fapp0 R L R G F))
      (@Transf_cat
        L R
        (@comp_cat_fapp0 L R R (@id_func R) G)
        (@comp_cat_fapp0
          L R R
          (@comp_cat_fapp0 R L R G F)
          G))
      (@comp_cat_con_fapp1_func
        L R R
        G
        (@id_func R)
        (@comp_cat_fapp0 R L R G F))
      (@unit_adj_transf R L F G J));

// Selected comonad of an adjunction, on the target L of the left adjoint.
// The witness is stable; its Monad observations below expose the exact dual
// operations without a transparent double-Op evidence path.
injective symbol adjunction_comonad
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@Comonad
      L
      (@comp_cat_fapp0 L R L F G));

// Underlying Monad-on-opposite observations agree propositionally with the
// dual adjunction operations. Runtime rules at an explicit `Op_cat L` index
// would overlap category-head normalization, so this boundary stays as
// equality evidence.
constant symbol adjunction_comonad_unit_op_path
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@=
      (Transf
        (@id_func (Op_cat L))
        (@Op_func L L (@comp_cat_fapp0 L R L F G)))
      (@unit_monad_transf
        (Op_cat L)
        (@Op_func L L (@comp_cat_fapp0 L R L F G))
        (@adjunction_comonad R L F G J))
      (@Op_transf
        L L
        (@comp_cat_fapp0 L R L F G)
        (@id_func L)
        (@counit_adj_transf R L F G J)));

constant symbol adjunction_comonad_mult_op_path
  [R L : Cat]
  [F : τ (@Functor R L)]
  [G : τ (@Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (@=
      (Transf
        (@comp_cat_fapp0
          (Op_cat L)
          (Op_cat L)
          (Op_cat L)
          (@Op_func L L (@comp_cat_fapp0 L R L F G))
          (@Op_func L L (@comp_cat_fapp0 L R L F G)))
        (@Op_func L L (@comp_cat_fapp0 L R L F G)))
      (@mult_monad_transf
        (Op_cat L)
        (@Op_func L L (@comp_cat_fapp0 L R L F G))
        (@adjunction_comonad R L F G J))
      (@Op_transf
        L L
        (@comp_cat_fapp0 L R L F G)
        (@comp_cat_fapp0
          L L L
          (@comp_cat_fapp0 L R L F G)
          (@comp_cat_fapp0 L R L F G))
        (@adjunction_comonad_comult_transf R L F G J)));

// Stable standard observations compute directly for the concrete instance.
rule @counit_comonad_transf
      $L _
      (@adjunction_comonad $R $L $F $G $J)
  ↪ @counit_adj_transf $R $L $F $G $J;

rule @comult_comonad_transf
      $L _
      (@adjunction_comonad $R $L $F $G $J)
  ↪ @adjunction_comonad_comult_transf $R $L $F $G $J;
