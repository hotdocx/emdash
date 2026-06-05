/*
  m- / emdash3.2
  Directed-family mixed-variance v3.2 migration draft.

  This file began as a fork of the retired v3.1 baseline.  It is now the active
  v3.2 development; the v3.1 file and original HOM/FAM/PI/CONST plan are
  archived historical baselines rather than current design authorities.  This file uses
  directed Cat-valued families directly:

    Functor_cat K Cat_cat ↪ Catd_cat K.

  Canonical surface syntax authority:
    reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md

  Current surface-notation summary:
    A ⊢ B                         = Functor_cat A B
    z :^n Z ; E[z] ⊢ D[z]         = Functord_cat E D
    Π (z :^n Z), D[z]             = Pi_cat D
    a ->^C b                      = Hom_cat C a b
    aa[z^-] ->_[z]^R bb[z]        = Hom_catd R aa bb
    A[z^-] ⊢_[z] B[z]             = Functor_catd A B
    F => G                        = Transf_cat F G
    FF[z^-] =>_[z] GG[z]          = Transf_catd A B FF GG

  Diagnostic `assert` checks live in emdash3_2_checks.lp.
*/

flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;

/*
  Ported working conventions from emdash2.lp

  This file is intentionally kernel-like: primitives stay small, and
  computational behavior is made explicit by rewrite and unification rules.
  Comments should name the categorical intent, but rules should stay close to
  the stable heads actually used by Lambdapi.

  Surface reading for this directed-family draft:
    - `E[x]` means `Fibre_cat E x`, for `E : Catd Z`.
    - `F[x]` means `fapp0 F x`, for an ordinary functor.
    - `ϵ[x]` means the diagonal component extracted by `tapp0_fapp0 x ϵ`.
    - `homd_int FF`, for `FF : Functord D E`, follows
      `homd_src_func`, `homd_src_sec`, `homd_tgt_func`, then `homd_`.

  Rewrite hygiene:
    - Lambdapi rule LHSs are matched and typechecked modulo conversion.
      Over-specifying inferred/implicit arguments can force expensive
      conversion problems, or make a rule fail to match after the inferred term
      reduces to a canonical expression.
    - Keep inferred/implicit arguments on rule LHSs as `_` unless they are
      essential discriminators.
    - In particular, do not spell defined aliases or reducible compound
      expressions in implicit LHS slots just because the rule typechecks.
      Such a rule can be accepted but later fail to fire when Lambdapi infers
      the same slot through a different normal form. Match on the stable head
      or explicit data argument instead, and let typing/unification recover
      the implicit endpoint.
    - If there are multiple inferred arguments in a nested expression, check
      all of them.  Omitting only one brittle argument is often not enough.
    - Be especially cautious when an implicit argument contains a reducible
      subterm such as `fapp0 F x`, `comp_cat_fapp0 F G`, `Functor_catd ...`,
      `HomPresheaf_catd_func ...`, or `Homd_target_catd ...`, or a compound
      canonical expression such as `Op_cat (Hom_cat ...)`.
    - When an explicit source/target category slot is needed for an assertion
      or rule, prefer the canonical normal form (`Hom_cat ...`,
      `Functord_cat ...`) over a reducible readability wrapper such as
      `Fibre_cat (DefinedAlias ...) k`.  The wrapper may compute in isolation
      but still make conversion search brittle in nested `fapp0` slots.
    - Prefer small projection rules with stable heads over one large nested
      redex. The homd projection path is split into `tapp0_fapp0` and `fapp0`
      folds; surface `piapp0` notation unfolds through `tapp0_fapp0`.
    - Prefer semantic definitions first.  Add a primitive/stable head only
      when a focused probe shows a real discrimination or performance need.
      If the issue is a missing projection rule (for example capped
      `fapp1_fapp0` for a constructor that already has `fapp1_func`), add that
      smaller projection instead of replacing the semantic definition.
    - Do not duplicate a semantic body in helper aliases.  Define readable
      aliases through the named semantic constructor so later corrections have
      one source of truth.
    - Probe nontrivial rules in a temporary copy first, with a bounded
      `lambdapi check` and a focused assertion for the expected normal form. A
      rule that typechecks but fails or times out on its intended assertion is
      not ready for this file.
    - During probes and debugging, explicit implicit arguments are useful:
      they make inferred categories, endpoints, and family indices visible in
      error messages. After the rule is stable, prefer the minimal form that
      still typechecks quickly and still matches the intended normal forms.
    - To audit whether an existing rule is still used, first search for likely
      downstream redexes and normal forms, then remove only that rule in a
      temporary copy and run a bounded check. Treat the first failing
      rule/assertion as the concrete dependency to document before deleting the
      temporary file.

  Stable heads and unification helpers:
    - Stable heads are the intended normal forms for operations that later
      rules need to recognize (`comp_cat_fapp0`, `tapp0_fapp0`,
      `homd_src_func`, `homd_src_sec`, `homd_tgt_func`).
    - Classifier wrappers such as `Hom`, `Functor`, `Catd`, `Functord`,
      `Transf`, and `Transfd` are injective heads.  This replaces direct
      wrapper-level unification rules.
    - Controlled `Obj`-inversion unification rules for chosen category heads
      (`Hom_cat`, `Functor_cat`, `Catd_cat`, `Functord_cat`, `Transf_cat`,
      `Transfd_cat`) are elaboration aids.  They are not semantic
      claims that `Obj` is globally injective. Avoid adding this style of rule
      for notation-only heads such as `Fibre_cat`: equality of fibre object
      categories should not force equality of the whole family and base index.
    - If a concrete constructor does not reduce early enough and needs one of
      these unification helpers, that is usually a signal to add a computation
      rule or introduce a smaller stable head.

  Omega-friendly normalization:
    - Prefer functor-level folds over capped pointwise rewrites when the result
      must remain iterable to higher cells.  A rule whose RHS is just
      `fapp0 (...) cell` computes one selected cell but can lose the functor
      object that would support another hom-action.
    - Use pointwise endpoint notation only when the current construction
      genuinely needs an endpoint. Here `homd_` is defined by the semantic
      `hom_con` endpoint; internal rules should discriminate on `homd_int`.

  Naming conventions:
    - Categories use uppercase letters (`A B C K Z`), with `Z` often the base.
    - Directed Cat-valued families use `E D A B` depending on variance; fibre
      objects are usually lowercase `u v`.
    - Ordinary functors use `F G`; transfors use Greek names such as `ϵ η`.
    - Projection/application heads follow the v2 pattern:
      `fapp*` for ordinary functors, `tapp*` for transfors, `piapp0` for a
      section of a `Pi_cat`, and `homd_*` for the dependent-hom projection
      pipeline.
*/

/*
  Maintenance inventory (v3.2)

  For each Cat-valued constructor, decide which projections compute by rewrite
  and which remain abstract.  Use this as a checklist before adding new rules.

    - Core `Op_cat`, `Path_cat`, `Terminal_cat`, `Cat_cat`: object/hom and
      basic identity/composition behavior compute by rewrite.
    - `Functor_cat`: object encoding is abstract; homs reduce to `Transf_cat`.
      Use `fapp0`, `fapp1_func`, `fapp1_fapp0`, and `tapp*` projections rather
      than exposing a record of functor data.
    - `Transf_cat`: object encoding is abstract; diagonal components compute
      through `tapp0_fapp0`, including identity and vertical composition.
    - `Catd_cat K`: the canonical category of directed Cat-valued families,
      reached by reducing `Functor_cat K Cat_cat`; `Fibre_cat` is notation for
      the surface reading of `E[k]`.
    - `Pi_cat E`: notation for the canonical section category
      `Functord_cat (Const_catd K Terminal_cat) E`, surface
      `Π (k :^n K), E[k]`, i.e. terminal-shape
      `k :^n K ; 1[k] ⊢ E[k]`;
      section homs and projections therefore use the displayed-functor normal
      form directly.
    - `Pi_int_funcd` / `Pi_pullback_funcd`: internalized Pi over varying bases.
      `Pi_pullback_funcd` is the stable normal form for the semantic
      `Pullback_catd_func` action on `Pi_int_funcd`; its fold keeps reducible
      endpoint-family slots implicit.
    - `Sigma_cat E`: object decoding is Sigma-shaped; homs between total
      objects route through the endpoint `homd_`.
    - `Functor_catd` / `Functor_catd_func`: mixed-variance family formation
      is functorial in family arguments, not just an object-level recipe.
    - `Rep_catd_func` / `Rep_catd` / `PathOut_cat`: raw covariant
      representable and outgoing-arrow total category notation for directed
      induction. `Edge_catd_func` remains the pointwise-opposite variant used
      by presheaf/dependent-hom contravariance.
    - `CompTarget_catd`: the fixed-`x` composition target is a semantic
      `hom_con` alias over `Catd_cat Z`, not a primitive stable family head.
      Its readable capped-action helper `CompTarget_fapp1_func` is defined
      through `CompTarget_catd` and uses canonical `Functord_cat` endpoints.
    - `Edge_catd_func` / `HomPresheaf_catd_func`: internal opposite-edge and
      presheaf-family classifiers. Keep them as named constructor pipelines;
      do not inline them into rewrite-rule LHSs.
    - `Homd_target_section_catd` / `Homd_target_catd`: target-family
      readability and assertion handles for `homd_int`.  Projection-rule LHSs
      should keep inferred source/target family arguments implicit.
    - `homd_` is the generalized endpoint with an explicit displayed functor
      argument. The old one-family endpoint is represented by the identity
      specialization `homd_ (id_funcd E)`.
    - `FibCov_*`: the internal covariant fibre-transport package; it projects
      through `fib_cov_src_func` to the external `fib_cov_transf`, then to
      `fib_cov_tapp0_func`.
    - `tapp1_int_func_transf` / `fapp1_int_transf`: ordinary internal
      hom-action heads ported from v2, including stable object/hom action
      package heads.
    - `tdapp1_int_func_transfd` / `fdapp1_int_transfd`: displayed internal
      analogues targeting the generalized `homd_int` arity, also with stable
      object/hom action package heads.
    - `tdapp0_func` / `tdapp0_fapp0`: stable displayed component heads for
      the ordinary component evaluation of displayed transfors.
    - `Fibre_func` / `Fibre_transf` / `Fibre_transf_app`: derived fibre-level
      projections over `tapp0`/`tdapp0`, useful for later bridges but not
      rewrite discriminators.
    - `catd_transport_func`, `functord_transport_*`, and
      `fdapp1_int_cell`: generic base-arrow transport,
      naturality-route, and component-level laxity/coherence helpers for
      displayed functors. A whole-transfor laxity interface remains deferred
      until the source object `u` can be internalized cleanly.
    - Pointwise displayed-functor calculus: `Op_funcd` projects through
      `tapp0_fapp0` to ordinary fibre opposites, and `comp_catd_fapp0`
      projects pointwise to ordinary fibre composition. The semantic E/C
      outer-slot form validates; the D/C outer-slot form is not the intended
      general `E[x] ⊢ C[x]` projection.
    - Earlier diagnostic aliases `fdapp1_int_fibre_transf` /
      `fdapp1_int_fibre_app` and the terminal-specialized `piapp1_int_*`
      projection chain have been retired. The displayed route now stays at the
      generic `fdapp1_int_transfd`/`tdapp0_fapp0` layer.
    - `piapp1_func` / `piapp1_fapp0`: section action over a base arrow. The
      capped component is retained as surface notation; it is no longer a
      terminal-specialized kernel projection target.
    - `Terminal_catd K` and `piapp0` are readability definitions, not rewrite
      discriminators. Operational rules use the unfolded constant-terminal
      source or lower-level `tapp0_fapp0` folds.
    - Generic Sigma/Pi weakening helpers have basic stable beta assertions; any
      richer coherence helpers remain deferred until needed.
*/

// -------------------------------------------------------------------------------------------------
// 0. Groupoid universe and equality
// -------------------------------------------------------------------------------------------------

/*
  Core object/type universe.

  Surface/formula:
    a : Grpd       is a small groupoidal/type-like object classifier.
    τ a            is the ambient Lambdapi type of elements of a.
    Prop/P         are mapped to Grpd/τ for Lambdapi's inductive interface.
*/
constant symbol Grpd : TYPE;
injective symbol τ : Grpd → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Grpd;
builtin "P" ≔ τ;

/*
  Equality in the groupoid universe.

  Surface/formula:
    x = y          is equality/path type in a groupoid a.
    eq_refl x      is the reflexive path.
    ind_eq p P u   transports u : P y backwards along p : x = y.
    eq_trans p q   composes paths p : x = y and q : y = z.
*/
constant symbol = : Π [a: Grpd], τ a → τ a → Grpd;
notation = infix 10;

constant symbol eq_refl : Π [a: Grpd], Π x: τ a, τ (x = x);

// Equality eliminator/transport.
symbol ind_eq : Π [a: Grpd], Π [x: τ a], Π [y: τ a],
  τ (x = y) → Π p: (τ a → Grpd), τ (p y) → τ (p x);
rule ind_eq (eq_refl $x) $p $u ↪ $u;

// Equality/path transitivity.
symbol eq_trans : Π [a : Grpd], Π [x : τ a], Π [y : τ a], Π [z : τ a],
  τ (x = y) → τ (y = z) → τ (x = z)
≔ λ a x y z p q, ind_eq p (λ t : τ a, t = z) q;

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

// Object-level unit and natural numbers used by examples/probes, not by the
// categorical core itself.
inductive unit : TYPE ≔ | tt : unit;

constant symbol Unit_grpd : Grpd;
rule τ Unit_grpd ↪ unit;

inductive nat : TYPE ≔
| zero : nat
| succ : nat → nat;

// -------------------------------------------------------------------------------------------------
// 1. Core categories
// -------------------------------------------------------------------------------------------------

/*
  Core category interface.

  Surface/formula:
    A : Cat
    Obj(A)                    object classifier of A
    Hom_cat(A,x,y)            hom-category Hom_A(x,y), also written x ->^A y
    Hom(A,x,y)                object/type classifier of Hom_cat(A,x,y)
    id_A(x)                   identity arrow
    comp_fapp0(g,f)           composite g ∘ f
    Op_cat(A)                 A^op
*/
constant symbol Cat : TYPE;

symbol Obj : Cat → Grpd;

injective symbol Hom_cat : Π (A : Cat) (X_A Y_A : τ (Obj A)), Cat;

// Object/type classifier of a hom-category.
injective symbol Hom (A : Cat) (X_A Y_A : τ (Obj A)) : Grpd
≔ Obj (Hom_cat A X_A Y_A);

/*
  Inference-helper policy:
  These unification rules are local elaboration aids for chosen heads such as
  `Hom_cat`, `Functor_cat`, and `Transf_cat`. They should be read as controlled
  "associativity of Obj" hints, not as global semantic injectivity claims for
  arbitrary category constructors.
*/
unif_rule Obj (Hom_cat $A $X $Y) ≡ Obj (Hom_cat $A' $X' $Y') ↪ [ $A ≡ $A'; $X ≡ $X'; $Y ≡ $Y' ];

injective symbol id : Π (A : Cat), Π (X_A: τ (Obj A)), τ (Hom A X_A X_A);

symbol comp_fapp0 : Π [A : Cat], Π [X_A Y_A : τ (Obj A)], Π [Z_A: τ (Obj A)],
  Π (g: τ (Hom A Y_A Z_A)), Π (f: τ (Hom A X_A Y_A)),
  τ (Hom A X_A Z_A);

// Opposite category.
injective symbol Op_cat : Cat → Cat;
rule Op_cat (Op_cat $A) ↪ $A;
rule Obj (Op_cat $A) ↪ Obj $A;
rule Hom_cat (Op_cat $A) $X $Y ↪ Hom_cat $A $Y $X;
rule @id (Op_cat $A) $X ↪ @id $A $X;
rule @comp_fapp0 (Op_cat $A) $X $Y $Z $g $f ↪ @comp_fapp0 $A $Z $Y $X $f $g;

// Path categories internalize HoTT equality as a groupoidal category.
//
// Surface/formula:
//   Path_cat(A) has objects x : A and arrows p : x = y.
injective symbol Path_cat : Grpd → Cat;
rule Obj (Path_cat $A) ↪ $A;
rule Hom_cat (Path_cat $A) $x $y ↪ Path_cat ($x = $y);
rule @id (Path_cat $A) $x ↪ eq_refl $x;
rule @comp_fapp0 (Path_cat $A) $x $y $z $q $p ↪ eq_trans $p $q;
rule Op_cat (Path_cat $A) ↪ Path_cat $A;

// Core groupoid of objects of a category.
//
// Surface/formula:
//   Core_cat(C) = Path_cat(Obj(C)).
symbol Core_cat (C : Cat) : Cat ≔ Path_cat (Obj C);

/*
  Path-category computation laws.

  Surface/formula:
    Obj(Path(A)) = A
    Hom_Path(A)(x,y) = Path(x,y)
    id_x = refl_x
    q ∘ p = eq_trans(p,q)
*/

// -------------------------------------------------------------------------------------------------
// 2. Ordinary functors and universe categories
// -------------------------------------------------------------------------------------------------

/*
  Ordinary functor category and classifier.

  Surface/formula:
    Functor_cat(A,B)       = A ⊢ B
    Functor(A,B)           = Obj(A ⊢ B)
    F[x]                   = fapp0 F x
    F[X,Y]                 = fapp1_func F : Hom_A(X,Y) ⊢ Hom_B(F[X],F[Y])
    F[f]                   = fapp1_fapp0 F f
*/
injective symbol Functor_cat : Π (A B : Cat), Cat;

injective symbol Functor (A B : Cat) : Grpd
≔ Obj (Functor_cat A B);

unif_rule Obj (Functor_cat $A $B) ≡ Obj (Functor_cat $A' $B') ↪ [ $A ≡ $A'; $B ≡ $B' ];

/*
  Mathematical notation:
    F : A ⊢ B                 means F : Functor(A,B)
    F[x]                      = fapp0 F x
    F₁[X,Y]                   = fapp1_func F : Hom_A(X,Y) ⊢ Hom_B(F[x],F[y])
    F[f]                      = fapp1_fapp0 F f
*/
symbol fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  τ (Obj A) → τ (Obj B);

symbol fapp1_func : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  τ (Functor (Hom_cat A X_A Y_A) (Hom_cat B (fapp0 F_AB X_A) (fapp0 F_AB Y_A)));

// Capped arrow action of a functor: F[f].
symbol fapp1_fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  Π (f : τ (Hom A X_A Y_A)),
  τ (Hom B (fapp0 F_AB X_A) (fapp0 F_AB Y_A));

rule fapp0 (fapp1_func $F_AB) $f ↪ fapp1_fapp0 $F_AB $f;

// Strict functoriality, oriented as cut elimination.
rule @fapp1_fapp0 $A $B $F $X $X (@id $A $X)
  ↪ @id $B (@fapp0 $A $B $F $X);

rule @comp_fapp0
      $B
      (@fapp0 $A $B $F $X)
      (@fapp0 $A $B $F $Y)
      (@fapp0 $A $B $F $Z)
      (@fapp1_fapp0 $A $B $F $Y $Z $g)
      (@fapp1_fapp0 $A $B $F $X $Y $f)
  ↪ @fapp1_fapp0
      $A
      $B
      $F
      $X
      $Z
      (@comp_fapp0 $A $X $Y $Z $g $f);

/*
  Universe classifiers and their category structures.

  Surface/formula:
    Grpd_cat has Obj(Grpd_cat) = Grpd and homs are ordinary functions.
    Cat_cat  has Obj(Cat_cat)  = Cat  and Hom(A,B) = A ⊢ B.
*/

// Category of groupoid/type classifiers.
constant symbol Grpd_cat : Cat;
injective symbol Grpd_grpd : Grpd ≔ Obj Grpd_cat;
rule τ (Obj Grpd_cat) ↪ Grpd;
rule τ (Obj (Hom_cat Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);

// Category of categories.
constant symbol Cat_cat : Cat;
injective symbol Cat_grpd  : Grpd ≔ Obj Cat_cat;
rule τ (Obj Cat_cat)  ↪ Cat;
rule Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;

/*
  Universe-category object and hom computations.

  Surface/formula:
    Obj(Grpd_cat) = Grpd
    Obj(Cat_cat)  = Cat
    Hom_Cat(A,B)  = A ⊢ B.
*/

// Directed Cat-valued families are canonical Cat-valued functors.
//
// Surface/formula:
//   Catd_cat(K) = K ⊢ Cat
//   Catd(K)     = Obj(Catd_cat(K))
//   E[k]        = fapp0 E k, usually via Fibre_cat E k.
injective symbol Catd_cat (K : Cat) : Cat;

injective symbol Catd (K : Cat) : Grpd
≔ Obj (Catd_cat K);

rule Functor_cat $K Cat_cat ↪ @Catd_cat $K;

unif_rule Obj (@Catd_cat $K) ≡ Obj (@Catd_cat $K') ↪ [ $K ≡ $K' ];

// Natural/displayed families of functors between directed Cat-valued families.
//
// Surface/formula:
//   Functord_cat(E,D) = k :^n K ; E[k] ⊢ D[k]
//   Functord(E,D)     = Obj(Functord_cat(E,D)).
injective symbol Functord_cat [K : Cat] (E D : τ (Catd K)) : Cat;

injective symbol Functord [K : Cat] (E D : τ (Catd K)) : Grpd
≔ Obj (@Functord_cat K E D);

unif_rule Obj (@Functord_cat $K $E $D) ≡ Obj (@Functord_cat $K' $E' $D')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D' ];

// `Catd_cat K` is the canonical normal form of `Functor_cat K Cat_cat`.
// Therefore `Hom_cat (Catd_cat K) E D` does not route through a direct
// `Transf_cat K Cat_cat E D` rewrite. The ordinary-functor route
// `Hom_cat (Functor_cat K Cat_cat) E D ↪ Transf_cat K Cat_cat E D` and the
// directed-family route below both join at `Functord_cat K E D`.
rule Hom_cat (@Catd_cat $K) $E $D ↪ @Functord_cat $K $E $D;

constant symbol id_funcd [K : Cat] [E : τ (Catd K)] : τ (Functord E E);
rule @id (@Catd_cat $K) $E ↪ @id_funcd $K $E;

// Displayed-functor composition.
symbol comp_catd_fapp0 [K : Cat] [E D : τ (Catd K)] [C : τ (Catd K)]
  (FF : τ (Functord D C)) (GG : τ (Functord E D)) : τ (Functord E C);

// Stable displayed-composition head, parallel to `comp_cat_fapp0`.
rule @comp_fapp0 (@Catd_cat $K) $E $D $C $FF $GG
  ↪ @comp_catd_fapp0 $K $E $D $C $FF $GG;

rule @comp_catd_fapp0 $K $E $E $C $FF (@id_funcd $K $E)
  ↪ $FF;
rule @comp_catd_fapp0 $K $E $D $D (@id_funcd $K $D) $GG
  ↪ $GG;

// Natural/displayed families of transformations, i.e. modifications between
// directed-family functors.
//
// Surface/formula:
//   Transfd_cat(FF,GG) = k :^n K ; FF[k] => GG[k]
//   Transfd(FF,GG)     = Obj(Transfd_cat(FF,GG)).
injective symbol Transfd_cat [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D)) : Cat;

injective symbol Transfd [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D)) : Grpd
≔ Obj (@Transfd_cat K E D FF GG);

unif_rule Obj (@Transfd_cat $K $E $D $FF $GG) ≡ Obj (@Transfd_cat $K' $E' $D' $FF' $GG')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D'; $FF ≡ $FF'; $GG ≡ $GG' ];

rule Hom_cat (@Functord_cat $K $E $D) $FF $GG
  ↪ @Transfd_cat $K $E $D $FF $GG;

// Stable displayed identity. The ordinary identity at a displayed-functor
// category folds here when that category is still visible; terminal-source
// section cases can use this head directly after Functord_cat contracts to
// Pi_cat.
constant symbol id_transfd [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : τ (@Transfd K E D FF FF);

rule @id (@Functord_cat $K $E $D) $FF
  ↪ @id_transfd $K $E $D $FF;

/*
  Directed-family category and displayed-arrow normal forms.

  Surface/formula:
    K ⊢ Cat = Catd_cat(K)
    Hom_Catd(E,D) = k :^n K ; E[k] ⊢ D[k]
    Hom_Functord(FF,GG) = k :^n K ; FF[k] => GG[k].
*/

/*
  Ordinary identity/composition in Cat_cat.

  Surface/formula:
    id_func(A)             = id_A : A ⊢ A
    comp_cat_fapp0(F,G)    = F ∘ G
    (F ∘ G)[x]             = F[G[x]]
    (F ∘ G)[f]             = F[G[f]]
*/
constant symbol id_func [A: Cat] : τ (Functor A A);
rule @id Cat_cat $A ↪ @id_func $A;
rule fapp0 (@id_func $A) $xA ↪ $xA;
rule @fapp1_fapp0 $A $A (@id_func $A) $x $y $p ↪ $p;

symbol comp_cat_fapp0 [A B : Cat] [C : Cat]
  (F : τ (Functor B C)) (G : τ (Functor A B)) : τ (Functor A C);

rule @comp_fapp0 Cat_cat $A $B $C $F $G ↪ @comp_cat_fapp0 $A $B $C $F $G;
rule @comp_cat_fapp0 $A $B $B (@id_func $B) $F ↪ $F;
rule @comp_cat_fapp0 $A $A $C $F (@id_func $A) ↪ $F;
rule @fapp0 $A $C (@comp_cat_fapp0 $A $B $C $F $G) $x ↪ @fapp0 $B $C $F (@fapp0 $A $B $G $x);
rule @fapp1_fapp0 $A $C (@comp_cat_fapp0 $A $B $C $F $G) $x $y $f
  ↪ @fapp1_fapp0
      $B
      $C
      $F
      (@fapp0 $A $B $G $x)
      (@fapp0 $A $B $G $y)
      (@fapp1_fapp0 $A $B $G $x $y $f);

rule @comp_fapp0 $A $Y $Y $Z $g (@id $A $Y) ↪ $g;
rule @comp_fapp0 $A $X $Z $Z (@id $A $Z) $f ↪ $f;

// Ordinary opposite functor action.
//
// Surface/formula:
//   Op_func(F) : A^op ⊢ B^op
//   Op_func(F)[x] = F[x]
//   Op_func(F)[f^op] = F[f]^op.
injective symbol Op_func : Π [A B : Cat],
  τ (Functor A B) → τ (Functor (Op_cat A) (Op_cat B));

rule Op_func (@Op_func $A $B $F) ↪ $F;
rule @fapp0 _ _ (@Op_func $A $B $F) $xA ↪ @fapp0 $A $B $F $xA;
rule @fapp1_func _ _ (@Op_func $A $B $F) $X $Y ↪ @fapp1_func $A $B $F $Y $X;
rule @fapp1_fapp0 _ _ (@Op_func $A $B $F) $X $Y $f
  ↪ @fapp1_fapp0 $A $B $F $Y $X $f;
rule @Op_func _ _ (@id_func $A) ↪ @id_func (Op_cat $A);
rule @Op_func _ _ (@comp_cat_fapp0 $A $B $C $F $G)
  ↪ comp_cat_fapp0 (Op_func $F) (Op_func $G);

// Terminal category and points-as-functors are needed to derive unary homs from
// binary homs.
//
// Surface/formula:
//   1 = Terminal_cat
//   Terminal_func(A) : A ⊢ 1
//   Obj_func(y) : 1 ⊢ Y picks out y : Obj(Y).
constant symbol Terminal_cat : Cat;
rule Op_cat Terminal_cat ↪ Terminal_cat;
rule Obj Terminal_cat ↪ Unit_grpd;
rule Hom_cat Terminal_cat _ _ ↪ Terminal_cat;

// Unique object of the terminal category.
constant symbol Terminal_obj : τ (Obj Terminal_cat);
rule @id Terminal_cat _ ↪ Terminal_obj;
rule @comp_fapp0 Terminal_cat _ _ _ _ _ ↪ Terminal_obj;

// Unique functor into the terminal category.
injective symbol Terminal_func : Π (A : Cat), τ (Functor A Terminal_cat);
rule @Op_func _ _ (@Terminal_func $A) ↪ @Terminal_func (Op_cat $A);

// Evaluation at a fixed object, as a functor out of a functor category.
//
// Surface/formula:
//   fapp0_func(x)[F] = F[x].
symbol fapp0_func : Π [A B : Cat],
  τ (Obj A) → τ (Functor (Functor_cat A B) B);
rule fapp0 (fapp0_func $x) $F ↪ fapp0 $F $x;

// Constant functor, used by constant directed families without capping the
// hom-action too early.
//
// Surface/formula:
//   Const_func(b) : A ⊢ B
//   Const_func(b)[x] = b
//   Const_func(b)[f] = id_b.
injective symbol Const_func [A B : Cat] (b : τ (Obj B)) : τ (Functor A B);
rule @fapp0 $A $B (@Const_func $A $B $b) $_ ↪ $b;
rule @fapp1_func $A $B (@Const_func $A $B $b) $x $y
  ↪ @Const_func
      (Hom_cat $A $x $y)
      (Hom_cat $B $b $b)
      (@id $B $b);
rule @fapp1_fapp0 $A $B (@Const_func $A $B $b) $x $y $_ ↪ @id $B $b;
rule @Op_func $A $B (@Const_func $A $B $b)
  ↪ @Const_func (Op_cat $A) (Op_cat $B) $b;
rule @comp_cat_fapp0 $A $B $C $F (@Const_func $A $B $b)
  ↪ @Const_func $A $C (@fapp0 $B $C $F $b);
rule @comp_cat_fapp0 $A $B $C (@Const_func $B $C $c) $G
  ↪ @Const_func $A $C $c;

// Point object as a functor from the terminal category.
//
// Surface/formula:
//   Obj_func(y) = const_1(y) : 1 ⊢ Y.
injective symbol Obj_func [Y : Cat] (y : τ (Obj Y)) : τ (Functor Terminal_cat Y)
≔ @Const_func Terminal_cat Y y;

// Internalized opposite as a functor in Cat.
//
// Surface/formula:
//   op : Cat ⊢ Cat
//   op[A] = A^op
//   op[F] = F^op.
constant symbol op : τ (Functor Cat_cat Cat_cat);
rule @fapp0 Cat_cat Cat_cat op $A ↪ Op_cat $A;
rule @fapp1_fapp0 Cat_cat Cat_cat op $A $B $F ↪ @Op_func $A $B $F;

// Internalized ordinary functor-category formation. The total package has no
// recoverable parameters; the partial stage is injective so equality of
// packages can recover the fixed source category.
//
// Surface/formula:
//   Functor_cat_func[A][B] = A ⊢ B.
constant symbol Functor_cat_func : τ (Functor (Op_cat Cat_cat) (Functor_cat Cat_cat Cat_cat));

injective symbol Functor_cat_fapp0_func (A : Cat) : τ (Functor Cat_cat Cat_cat);

rule @fapp0 _ _ Functor_cat_func $A
  ↪ Functor_cat_fapp0_func $A;
rule @fapp0 Cat_cat Cat_cat (Functor_cat_fapp0_func $A) $B
  ↪ Functor_cat $A $B;

// Internalized-x prerequisite: directed-family category formation as a
// universe-level functor.
//
// Surface/formula:
//   Catd_cat_func : Cat^op ⊢ Cat
//   Catd_cat_func[K] = Catd(K) = (K ⊢ Cat)
//   Catd_cat_func[F : A ⊢ B] = F^* : Catd(B) ⊢ Catd(A)
//
// This is the internal package that lets later constructions vary the base
// category. It is obtained by evaluating the internalized ordinary
// functor-category constructor at Cat_cat.
symbol Catd_cat_func : τ (Functor (Op_cat Cat_cat) Cat_cat)
≔ @comp_cat_fapp0
     (Op_cat Cat_cat)
     (Functor_cat Cat_cat Cat_cat)
     Cat_cat
     (@fapp0_func Cat_cat Cat_cat Cat_cat)
     Functor_cat_func;

// Curried postcomposition in Cat, used to build constructor pipelines.
//
// Surface/formula:
//   comp_cat_cov_func(G) : (X ⊢ Y) ⊢ (X ⊢ Z)
//   comp_cat_cov_func(G)[F] = G ∘ F.
symbol comp_cat_cov_func : Π [X Y Z : Cat],
  Π (G : τ (Functor Y Z)),
  τ (Functor (Functor_cat X Y) (Functor_cat X Z));

rule fapp0 (@comp_cat_cov_func $X $Y $Z $G) $F
  ↪ comp_cat_fapp0 $G $F;

// Postcomposition packaged as a functor in the postcomposing functor.
//
// Surface/formula:
//   comp_cat_cov_func_func[X,Y,Z][G] = comp_cat_cov_func(G)
//   : (Y ⊢ Z) ⊢ ((X ⊢ Y) ⊢ (X ⊢ Z)).
symbol comp_cat_cov_func_func [X Y Z : Cat]
  : τ (Functor
      (Functor_cat Y Z)
      (Functor_cat (Functor_cat X Y) (Functor_cat X Z)));

rule fapp0 (@comp_cat_cov_func_func $X $Y $Z) $G
  ↪ @comp_cat_cov_func $X $Y $Z $G;

// Precomposition by a fixed functor.
//
// Surface/formula:
//   comp_cat_con_func(F)[G] = G o F
//   : (Y ⊢ Z) ⊢ (X ⊢ Z).
symbol comp_cat_con_func [X Y Z : Cat]
  (F : τ (Functor X Y))
  : τ (Functor (Functor_cat Y Z) (Functor_cat X Z));

rule fapp0 (@comp_cat_con_func $X $Y $Z $F) $G
  ↪ @comp_cat_fapp0 $X $Y $Z $G $F;

// Internalized pointwise opposite on directed families. This is the packaged
// functorial version of `Op_catd`; the object-level result remains the
// canonical normal form.
//
// Surface/formula:
//   Op_catd_func(Z)[E] = E^op.
injective symbol Op_catd_func (Z : Cat) : τ (Functor (Catd_cat Z) (Catd_cat Z));

rule @comp_cat_cov_func $Z Cat_cat Cat_cat op
  ↪ @Op_catd_func $Z;

// -------------------------------------------------------------------------------------------------
// 3. Curried internal hom
// -------------------------------------------------------------------------------------------------

/*
  Ordinary internal hom classifiers.

  Surface/formula:
    hom_(F,W)[y]          = Hom_A(W,F[y])
    hom_postcomp_func(f)(g)= F[f] o g
    hom_con(W,F)[y]       = Hom_A(F[y],W)
    hom_int(F)[W][y]      = Hom_A(W,F[y])
    hom_precomp_func(f)(g)= g ∘ f

  `hom_int(F)` is the internalized functorial package
  A^op ⊢ (B ⊢ Cat). Its surface reading is:

    W :^n A^op ; 1[W] ⊢ (y :^n B ; 1[y] ⊢ Hom_A(W,y))
*/
injective symbol hom_ [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  : τ (Functor B Cat_cat);
rule @fapp0 $B Cat_cat (@hom_ $A $B $F $W) $y
  ↪ Hom_cat $A $W (@fapp0 $B $A $F $y);

// Ordinary hom-action computes by postcomposition:
// ((Hom_A(W,F-))_1 f)_0 g ↪ (F f) ∘ g.
rule fapp0 (@fapp1_fapp0 $B Cat_cat (@hom_ $A $B $F $W) $X $Y $f) $g
  ↪ comp_fapp0 (fapp1_fapp0 $F $f) $g;

/*
  Stable covariant hom-action projections.

  Mathematical notation:
    hom_postcomp_tele_func(F,W,X,Y)
      : Hom_B(X,Y) ⊢ (Hom_A(W,F[X]) ⊢ Hom_A(W,F[Y]))

    hom_postcomp_func(F,W,X,Y,f)[g] = F[f] ∘ g

    hom_postcomp_fapp1_func(F,W,X,Y,f,g,h)
      : Hom(g,h) ⊢ Hom(F[f] ∘ g, F[f] ∘ h)

  Faithful surface syntax:
    Hom_A(W,F[-])[f](g)

  This is the functorial-in-f head for postcomposition. It keeps the arrow
  f : X ->^B Y visible long enough to expose the whole functor
  Hom_A(W,F[X]) ⊢ Hom_A(W,F[Y]), rather than capping immediately at a
  single g.
*/
symbol hom_postcomp_tele_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  : τ (Functor
      (Hom_cat B X Y)
      (Functor_cat
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A W (@fapp0 B A F Y))));

rule @fapp1_func $B Cat_cat (@hom_ $A $B $F $W) $X $Y
  ↪ @hom_postcomp_tele_func $A $B $F $W $X $Y;

symbol hom_postcomp_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  (f : τ (Hom B X Y))
  : τ (Functor
      (Hom_cat A W (@fapp0 B A F X))
      (Hom_cat A W (@fapp0 B A F Y)));

rule fapp0 (@hom_postcomp_tele_func $A $B $F $W $X $Y) $f
  ↪ @hom_postcomp_func $A $B $F $W $X $Y $f;

rule fapp0 (@hom_postcomp_func $A $B $F $W $X $Y $f) $g
  ↪ @comp_fapp0
      $A
      $W
      (@fapp0 $B $A $F $X)
      (@fapp0 $B $A $F $Y)
      (@fapp1_fapp0 $B $A $F $X $Y $f)
      $g;

symbol hom_postcomp_fapp1_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  (f : τ (Hom B X Y))
  [g h : τ (Hom A W (@fapp0 B A F X))]
  : τ (Functor
      (Hom_cat (Hom_cat A W (@fapp0 B A F X)) g h)
      (Hom_cat
        (Hom_cat A W (@fapp0 B A F Y))
        (@comp_fapp0
          A W (@fapp0 B A F X) (@fapp0 B A F Y)
          (@fapp1_fapp0 B A F X Y f)
          g)
        (@comp_fapp0
          A W (@fapp0 B A F X) (@fapp0 B A F Y)
          (@fapp1_fapp0 B A F X Y f)
          h)));

symbol hom_postcomp_fapp1_fapp0 [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  (f : τ (Hom B X Y))
  [g h : τ (Hom A W (@fapp0 B A F X))]
  (alpha : τ (Hom (Hom_cat A W (@fapp0 B A F X)) g h))
  : τ (Hom
      (Hom_cat A W (@fapp0 B A F Y))
      (@comp_fapp0
        A W (@fapp0 B A F X) (@fapp0 B A F Y)
        (@fapp1_fapp0 B A F X Y f)
        g)
      (@comp_fapp0
        A W (@fapp0 B A F X) (@fapp0 B A F Y)
        (@fapp1_fapp0 B A F X Y f)
        h));

rule @fapp1_func _ _ (@hom_postcomp_func $A $B $F $W $X $Y $f) $g $h
  ↪ @hom_postcomp_fapp1_func $A $B $F $W $X $Y $f $g $h;

rule fapp0 (@hom_postcomp_fapp1_func $A $B $F $W $X $Y $f $g $h) $alpha
  ↪ @hom_postcomp_fapp1_fapp0 $A $B $F $W $X $Y $f $g $h $alpha;

rule @fapp1_fapp0 _ _ (@hom_postcomp_func $A $B $F $W $X $Y $f) $g $h $alpha
  ↪ @hom_postcomp_fapp1_fapp0 $A $B $F $W $X $Y $f $g $h $alpha;

rule @hom_postcomp_tele_func Cat_cat Cat_cat (@id_func Cat_cat) $X $Y $Z
  ↪ @comp_cat_cov_func_func $X $Y $Z;

rule @hom_postcomp_func Cat_cat Cat_cat (@id_func Cat_cat) $X $Y $Z $G
  ↪ @comp_cat_cov_func $X $Y $Z $G;

/*
  Stable contravariant hom-action projections.

  Mathematical notation:
    hom_precomp_func(A,X,Y,Z,f)
      : Hom_A(Y,Z) ⊢ Hom_A(X,Z)

    hom_precomp_func(f)[g] = g ∘ f

    hom_precomp_fapp1_func(f,g,h)
      : Hom(g,h) ⊢ Hom(g ∘ f,h ∘ f)

  Faithful surface syntax:
    Hom_A(-,Z)[f](g)

  This is the represented-object action of hom_int. For f : X ->^A Y, the
  component at Z sends a map g : Y ->^A Z to g ∘ f.
*/
symbol hom_precomp_func [A : Cat] [X Y Z : τ (Obj A)]
  (f : τ (Hom A X Y))
  : τ (Functor (Hom_cat A Y Z) (Hom_cat A X Z));

rule @fapp0 (Hom_cat $A $Y $Z) (Hom_cat $A $X $Z)
      (@hom_precomp_func $A $X $Y $Z $f) $g
  ↪ @comp_fapp0 $A $X $Y $Z $g $f;

rule @hom_precomp_func Cat_cat $X $Y $Z $F
  ↪ @comp_cat_con_func $X $Y $Z $F;

symbol hom_precomp_fapp1_func [A : Cat] [X Y Z : τ (Obj A)]
  (f : τ (Hom A X Y))
  [g h : τ (Hom A Y Z)]
  : τ (Functor
      (Hom_cat (Hom_cat A Y Z) g h)
      (Hom_cat
        (Hom_cat A X Z)
        (@comp_fapp0 A X Y Z g f)
        (@comp_fapp0 A X Y Z h f)));

symbol hom_precomp_fapp1_fapp0 [A : Cat] [X Y Z : τ (Obj A)]
  (f : τ (Hom A X Y))
  [g h : τ (Hom A Y Z)]
  (alpha : τ (Hom (Hom_cat A Y Z) g h))
  : τ (Hom
      (Hom_cat A X Z)
      (@comp_fapp0 A X Y Z g f)
      (@comp_fapp0 A X Y Z h f));

rule @fapp1_func _ _ (@hom_precomp_func $A $X $Y $Z $f) $g $h
  ↪ @hom_precomp_fapp1_func $A $X $Y $Z $f $g $h;

rule fapp0 (@hom_precomp_fapp1_func $A $X $Y $Z $f $g $h) $alpha
  ↪ @hom_precomp_fapp1_fapp0 $A $X $Y $Z $f $g $h $alpha;

rule @fapp1_fapp0 _ _ (@hom_precomp_func $A $X $Y $Z $f) $g $h $alpha
  ↪ @hom_precomp_fapp1_fapp0 $A $X $Y $Z $f $g $h $alpha;

// Contravariant represented-object classifier.
//
// Surface/formula:
//   hom_con(W,F)[y] = Hom_A(F[y],W).
injective symbol hom_con [A : Cat] (W : τ (Obj A)) [B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat B) Cat_cat)
≔ @hom_ (Op_cat A) (Op_cat B) (@Op_func B A F) W;

// Internalized hom classifier.
//
// Surface/formula:
//   hom_int(F) : A^op ⊢ (B ⊢ Cat)
//   hom_int(F)[W][y] = Hom_A(W,F[y]).
injective symbol hom_int [A B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat A) (Catd_cat B));

rule @fapp0 _ _ (@hom_int $A $B $F) $W
  ↪ @hom_ $A $B $F $W;

/*
  Ordinary internal-hom computations.

  Surface/formula:
    hom_(F,W)[y] = Hom_A(W,F[y])
    hom_con(W,F)[y] = Hom_A(F[y],W)
    hom_int(F)[W][y] = Hom_A(W,F[y])
    hom_precomp_func(p)[q] = q o p.
*/

// -------------------------------------------------------------------------------------------------
// 4. Encoded Sigma types for object layers
// -------------------------------------------------------------------------------------------------

inductive τΣ_ [a : Grpd] (P : τ a → Grpd) : TYPE ≔
| Struct_sigma [a P] : Π (sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst)), @τΣ_ a P;
notation τΣ_ quantifier;

/*
  Encoded dependent pair type used for object-level Sigma data.

  Surface/formula:
    Σ x : a, P(x)
    Struct_sigma x u = (x,u)
    sigma_Fst(x,u)   = x
    sigma_Snd(x,u)   = u
*/
constant symbol Σ_ [a : Grpd] (P : τ a → Grpd) : Grpd;
notation Σ_ quantifier;
rule τ (Σ_ $P) ↪ τΣ_ $P;

injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;

// Second projection of an encoded dependent pair.
injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;

// -------------------------------------------------------------------------------------------------
// 4b. Ordinary binary products of categories
// -------------------------------------------------------------------------------------------------

/*
  Minimal ordinary product package.

  Surface/formula:
    Product_cat(A,B)              = A x B
    Obj(A x B)                    = Sigma x : Obj(A), Obj(B)
    Hom_{A x B}((x,u),(y,v))      = Hom_A(x,y) x Hom_B(u,v)
    id_{(x,u)}                    = (id_x,id_u)
    (g1,g2) o (f1,f2)             = (g1 o f1, g2 o f2)
    X ⊢ (A x B)                  = (X ⊢ A) x (X ⊢ B)

  Product-valued functors are represented by the product normal form above.
  Projection computation is attached to stable projection functor heads and to
  `sigma_Fst`/`sigma_Snd` consumer rules. Avoid a broad eta rule expanding
  arbitrary `fapp0 H i`; use the narrower paired-head rules below.
*/
injective symbol Product_cat : Π (A B : Cat), Cat;

rule Functor_cat $X (Product_cat $A $B)
  ↪ Product_cat (Functor_cat $X $A) (Functor_cat $X $B);

rule Obj (Product_cat $A $B)
  ↪ @Σ_ (Obj $A) (λ _ : τ (Obj $A), Obj $B);

rule Op_cat (Product_cat $A $B)
  ↪ Product_cat (Op_cat $A) (Op_cat $B);

symbol Product_projL [A B : Cat] (xy : τ (Obj (Product_cat A B)))
  : τ (Obj A)
≔ sigma_Fst xy;

symbol Product_projR [A B : Cat] (xy : τ (Obj (Product_cat A B)))
  : τ (Obj B)
≔ sigma_Snd xy;

injective symbol Product_pair [A B : Cat]
  (x : τ (Obj A)) (y : τ (Obj B))
  : τ (Obj (Product_cat A B))
≔ @Struct_sigma (Obj A) (λ _ : τ (Obj A), Obj B) x y;

injective symbol Product_projL_func [A B : Cat]
  : τ (Functor (Product_cat A B) A);

injective symbol Product_projR_func [A B : Cat]
  : τ (Functor (Product_cat A B) B);

// The identity functor of a product is the paired projection functor.
rule sigma_Fst (@id_func (Product_cat $A $B)) ↪ @Product_projL_func $A $B;
rule sigma_Snd (@id_func (Product_cat $A $B)) ↪ @Product_projR_func $A $B;

rule @fapp0 (Product_cat $A $B) $A (@Product_projL_func $A $B) $p
  ↪ sigma_Fst $p;

rule @fapp0 (Product_cat $A $B) $B (@Product_projR_func $A $B) $p
  ↪ sigma_Snd $p;

// Projection of a paired functor application.
rule sigma_Fst (@fapp0 $X (Product_cat $A $B) $H $i)
  ↪ @fapp0 $X $A (sigma_Fst $H) $i;

rule sigma_Snd (@fapp0 $X (Product_cat $A $B) $H $i)
  ↪ @fapp0 $X $B (sigma_Snd $H) $i;

// Application and hom-action for an explicitly paired functor.
rule @fapp0 $X (Product_cat $A $B) (Struct_sigma $F $G) $i
  ↪ Struct_sigma
      (@fapp0 $X $A $F $i)
      (@fapp0 $X $B $G $i);

rule Hom_cat (Product_cat $A $B) $p $q
  ↪ Product_cat
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

rule @fapp1_func $X (Product_cat $A $B) (Struct_sigma $F $G) $i $j
  ↪ Struct_sigma
      (@fapp1_func $X $A $F $i $j)
      (@fapp1_func $X $B $G $i $j);

rule @fapp1_fapp0 $X (Product_cat $A $B) (Struct_sigma $F $G) $i $j $p
  ↪ Struct_sigma
      (@fapp1_fapp0 $X $A $F $i $j $p)
      (@fapp1_fapp0 $X $B $G $i $j $p);

rule @fapp1_func (Product_cat $A $B) $A (@Product_projL_func $A $B) $p $q
  ↪ @Product_projL_func
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

rule @fapp1_func (Product_cat $A $B) $B (@Product_projR_func $A $B) $p $q
  ↪ @Product_projR_func
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

rule @fapp1_fapp0 (Product_cat $A $B) $A (@Product_projL_func $A $B) $p $q $h
  ↪ sigma_Fst $h;

rule @fapp1_fapp0 (Product_cat $A $B) $B (@Product_projR_func $A $B) $p $q $h
  ↪ sigma_Snd $h;

rule @id (Product_cat $A $B) (Struct_sigma $x $u)
  ↪ Struct_sigma (@id $A $x) (@id $B $u);

rule @comp_fapp0
      (Product_cat $A $B)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
      (Struct_sigma $z $w)
      (Struct_sigma $g1 $g2)
      (Struct_sigma $f1 $f2)
  ↪ Struct_sigma
      (@comp_fapp0 $A $x $y $z $g1 $f1)
      (@comp_fapp0 $B $u $v $w $g2 $f2);

// Pairing telescope for products. Its computation rules are installed later,
// after the constant-section machinery they project to is available.
symbol Product_pair_tele_func [A B : Cat]
  : τ (Functor A (Functor_cat B (Product_cat A B)));

// -------------------------------------------------------------------------------------------------
// 5. Ordinary transfors
// -------------------------------------------------------------------------------------------------

/*
  Ordinary transfor/natural-transformation category.

  Surface/formula:
    Transf_cat(F,G) = F => G
    Transf(F,G)     = Obj(F => G)

  For Cat-valued functors this reduces to the displayed-family category:
    Transf_cat(K,Cat,E,D) = Functord_cat(E,D).
*/
injective symbol Transf_cat : Π [A B : Cat], Π (F G : τ (Functor A B)), Cat;

injective symbol Transf [A B : Cat] (F G : τ (Functor A B)) : Grpd
≔ Obj (@Transf_cat A B F G);

// Controlled Obj-inversion for transformation categories. This is the
// emdash2 helper that lets projection rules keep source/target functors
// implicit, e.g. `@tapp0_fapp0 ... _ _ ...`, without forcing reducible
// compound family expressions into rewrite-rule LHSs.
unif_rule Obj (@Transf_cat $A $B $F $G) ≡ Obj (@Transf_cat $A' $B' $F' $G')
  ↪ [ $A ≡ $A'; $B ≡ $B'; $F ≡ $F'; $G ≡ $G' ];

rule Hom_cat (Functor_cat _ _) $F $G ↪ Transf_cat $F $G;
rule @Transf_cat $K Cat_cat $E $D ↪ @Functord_cat $K $E $D;

rule @Transf_cat $X (Product_cat $A $B) $F $G
  ↪ Product_cat
      (@Transf_cat $X $A (sigma_Fst $F) (sigma_Fst $G))
      (@Transf_cat $X $B (sigma_Snd $F) (sigma_Snd $G));

/*
  Cat-valued transfors reduce to displayed functors.

  Surface/formula:
    Transf(K,Cat,E,D) = Functord(E,D).
*/

/*
  Mathematical notation:
    ϵ : F => G
    tapp0_func(F,G,Y)         : Transf(F,G) ⊢ Hom_B(F[Y],G[Y])
    ϵ[Y]                      = tapp0_fapp0 Y ϵ
    (η ∘ ϵ)[Y]                = η[Y] ∘ ϵ[Y]
*/
symbol tapp0_func : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (Y : τ (Obj A)),
  τ (Functor (Transf_cat F G) (Hom_cat B (fapp0 F Y) (fapp0 G Y)));

symbol tapp0_fapp0 : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (Y : τ (Obj A)),
  Π (ϵ : τ (Obj (Transf_cat F G))),
  τ (Hom B (fapp0 F Y) (fapp0 G Y));

/*
  Design note: `tapp0_fapp0` is a primitive projection head, not a
  definitional abbreviation.  This follows emdash2: the head must remain
  visible so later rules can attach component computations directly to it.
*/
rule fapp0 (@tapp0_func $A $B $F $G $Y) $ϵ
  ↪ @tapp0_fapp0 $A $B $F $G $Y $ϵ;

rule sigma_Fst (@tapp0_fapp0 $X (Product_cat $A $B) $F $G $i $eta)
  ↪ @tapp0_fapp0 $X $A (sigma_Fst $F) (sigma_Fst $G) $i (sigma_Fst $eta);

rule sigma_Snd (@tapp0_fapp0 $X (Product_cat $A $B) $F $G $i $eta)
  ↪ @tapp0_fapp0 $X $B (sigma_Snd $F) (sigma_Snd $G) $i (sigma_Snd $eta);

// Hom-action of evaluation-at-an-object is component projection.
rule @fapp1_func _ $B (@fapp0_func $A $B $x) $F $G
  ↪ @tapp0_func $A $B $F $G $x;

rule @fapp1_fapp0 _ $B (@fapp0_func $A $B $x) $F $G $η
  ↪ @tapp0_fapp0 $A $B $F $G $x $η;

rule @tapp0_fapp0 $A $B $F $F $Y (@id (Functor_cat $A $B) $F)
  ↪ @id $B (@fapp0 $A $B $F $Y);

rule @tapp0_fapp0 $K Cat_cat $E $E $Y (@id_funcd $K $E)
  ↪ @id_func (@fapp0 $K Cat_cat $E $Y);

rule @tapp0_fapp0 $A $B $F $H $Y (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
  ↪ comp_fapp0
      (@tapp0_fapp0 $A $B $G $H $Y $η)
      (@tapp0_fapp0 $A $B $F $G $Y $ϵ);

// Component of `hom_int` along its contravariant represented-object argument.
// For f : X ->^A Y, the displayed functor Hom(Y,F-) ⊢ Hom(X,F-) is
// precomposition by f.
rule @tapp0_fapp0
      $B
      Cat_cat
      _
      _
      $b
      (@fapp1_fapp0 (Op_cat $A) (@Catd_cat $B)
        (@hom_int $A $B $F) $Y $X $f)
  ↪ @hom_precomp_func $A $X $Y (@fapp0 $B $A $F $b) $f;

// Component of `hom_int` in the represented object is precomposition.

// Reserved capped ordinary hom-action surface. It is not used by v3.2 rules
// yet.
//
// Surface/formula:
//   tapp1_fapp0(ϵ,f) : F[X] ->^B G[Y]
//
// The intended computation is the projected endpoint of
// `tapp1_int_func_transf`: evaluate the internal action at ϵ, project the
// resulting transfor at X and then Y, and finally apply the resulting hom
// functor to f. Keep it abstract until the external ordinary naturality API is
// promoted.
symbol tapp1_fapp0 : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π [X Y : τ (Obj A)],
  Π (ϵ : τ (Obj (Transf_cat F G))),
  Π (f : τ (Hom A X Y)),
  τ (Hom B (fapp0 F X) (fapp0 G Y));

// Functor-level off-diagonal ordinary transfor component.
//
// Surface/formula:
//   tapp1_func(ϵ,X,Y) : Hom_A(X,Y) ⊢ Hom_B(F[X],G[Y])
//   tapp1_func(ϵ,X,Y)[f] = tapp1_fapp0(ϵ,f).
symbol tapp1_func : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π [X Y : τ (Obj A)],
  Π (ϵ : τ (Obj (Transf_cat F G))),
  τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (fapp0 F X) (fapp0 G Y)));

rule fapp0 (@tapp1_func $A $B $F $G $X $Y $ϵ) $f
  ↪ @tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f;

rule sigma_Fst (@tapp1_func $X (Product_cat $A $B) $F $G $i $j $eta)
  ↪ @tapp1_func $X $A (sigma_Fst $F) (sigma_Fst $G) $i $j (sigma_Fst $eta);

rule sigma_Snd (@tapp1_func $X (Product_cat $A $B) $F $G $i $j $eta)
  ↪ @tapp1_func $X $B (sigma_Snd $F) (sigma_Snd $G) $i $j (sigma_Snd $eta);

rule @tapp1_func $A $B $F $F $X $Y (@id (Functor_cat $A $B) $F)
  ↪ @fapp1_func $A $B $F $X $Y;

/*
  Constant transfor induced by an arrow in the codomain.

  Mathematical notation:
    Const_transf_func(K,A,x,y)
      : Hom_A(x,y) ⊢ Transf(const x,const y)

    Const_transf(p)[k] = p
    Const_transf(p)[q] = p

  Faithful surface syntax:
    k :^n K ; 1[k] ⊢ (p : x ->^A y)

  The component and off-diagonal action are constant in the K-variable. This
  is the transfor-level counterpart of Const_func.
*/
symbol Const_transf_func [K A : Cat] [x y : τ (Obj A)]
  : τ (Functor
      (Hom_cat A x y)
      (@Transf_cat K A (@Const_func K A x) (@Const_func K A y)));

symbol Const_transf [K A : Cat] [x y : τ (Obj A)]
  (p : τ (Hom A x y))
  : τ (Transf (@Const_func K A x) (@Const_func K A y));

rule fapp0 (@Const_transf_func $K $A $x $y) $p
  ↪ @Const_transf $K $A $x $y $p;

rule @tapp0_fapp0 $K $A _ _ $k (@Const_transf $K $A $x $y $p)
  ↪ $p;

rule @tapp1_func $K $A _ _ $k $k' (@Const_transf $K $A $x $y $p)
  ↪ @Const_func (Hom_cat $K $k $k') (Hom_cat $A $x $y) $p;

rule @tapp1_fapp0 $K $A _ _ $k $k' (@Const_transf $K $A $x $y $p) $_
  ↪ $p;

/*
  Postcomposition of transfors by a fixed functor.

  Mathematical notation:
    comp_cat_cov_fapp1_func(G)
      : Transf(F,H) ⊢ Transf(G ∘ F, G ∘ H)

    comp_cat_cov_transf(G,eta) = G eta
    comp_cat_cov_transf(G,eta)[i] = G[eta[i]]

  Faithful surface syntax:
    eta : F => H
    G eta : G ∘ F => G ∘ H

  The name follows the ordinary `comp_cat_cov_func(G)` object action: the
  functor argument varies covariantly in the slot being postcomposed by G.
*/
symbol comp_cat_cov_fapp1_func [X Y Z : Cat]
  (G : τ (Functor Y Z))
  [F H : τ (Functor X Y)]
  : τ (Functor
      (@Transf_cat X Y F H)
      (@Transf_cat
        X Z
        (@comp_cat_fapp0 X Y Z G F)
        (@comp_cat_fapp0 X Y Z G H)));

symbol comp_cat_cov_transf [X Y Z : Cat]
  (G : τ (Functor Y Z))
  [F H : τ (Functor X Y)]
  (eta : τ (Transf F H))
  : τ (Transf
      (@comp_cat_fapp0 X Y Z G F)
      (@comp_cat_fapp0 X Y Z G H));

rule @hom_postcomp_fapp1_func Cat_cat Cat_cat (@id_func Cat_cat) $X $Y $Z $G $F $H
  ↪ @comp_cat_cov_fapp1_func $X $Y $Z $G $F $H;

rule @hom_postcomp_fapp1_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) $X $Y $Z $G $F $H $eta
  ↪ @comp_cat_cov_transf $X $Y $Z $G $F $H $eta;

rule @fapp1_func _ _ (@comp_cat_cov_func $X $Y $Z $G) $F $H
  ↪ @comp_cat_cov_fapp1_func $X $Y $Z $G $F $H;

rule fapp0 (@comp_cat_cov_fapp1_func $X $Y $Z $G $F $H) $eta
  ↪ @comp_cat_cov_transf $X $Y $Z $G $F $H $eta;

rule @fapp1_fapp0 _ _ (@comp_cat_cov_func $X $Y $Z $G) $F $H $eta
  ↪ @comp_cat_cov_transf $X $Y $Z $G $F $H $eta;

rule @tapp0_fapp0
      $X
      $Z
      _
      _
      $i
      (@comp_cat_cov_transf $X $Y $Z $G $F $H $eta)
  ↪ @fapp1_fapp0
      $Y
      $Z
      $G
      (@fapp0 $X $Y $F $i)
      (@fapp0 $X $Y $H $i)
      (@tapp0_fapp0 $X $Y $F $H $i $eta);

rule @tapp1_func
      $X
      $Z
      _
      _
      $i
      $j
      (@comp_cat_cov_transf $X $Y $Z $G $F $H $eta)
  ↪ @comp_cat_fapp0
      (Hom_cat $X $i $j)
      (Hom_cat $Y
        (@fapp0 $X $Y $F $i)
        (@fapp0 $X $Y $H $j))
      (Hom_cat $Z
        (@fapp0 $Y $Z $G (@fapp0 $X $Y $F $i))
        (@fapp0 $Y $Z $G (@fapp0 $X $Y $H $j)))
      (@fapp1_func
        $Y
        $Z
        $G
        (@fapp0 $X $Y $F $i)
        (@fapp0 $X $Y $H $j))
      (@tapp1_func $X $Y $F $H $i $j $eta);

rule @tapp1_fapp0
      $X
      $Z
      _
      _
      $i
      $j
      (@comp_cat_cov_transf $X $Y $Z $G $F $H $eta)
      $p
  ↪ @fapp1_fapp0
      $Y
      $Z
      $G
      (@fapp0 $X $Y $F $i)
      (@fapp0 $X $Y $H $j)
      (@tapp1_fapp0 $X $Y $F $H $i $j $eta $p);

/*
  Hom-action of postcomposition as a functor in the postcomposing functor.

  Mathematical notation:
    comp_cat_cov_func_func[X,Y,Z]
      : (Y ⊢ Z) ⊢ ((X ⊢ Y) ⊢ (X ⊢ Z))

    comp_cat_cov_func_func_transf(eta)
      : (G ∘ -) => (H ∘ -)

    comp_cat_cov_func_func_transf(eta)[F]
      = eta ∘ F : G ∘ F => H ∘ F.

  Faithful surface syntax:
    eta : G => H
    eta ∘ F : G ∘ F => H ∘ F

  Its object component at F is precomposition of eta by F, implemented by
  `comp_cat_con_transf(F,eta)`.
*/
symbol comp_cat_cov_func_func_fapp1_func [X Y Z : Cat]
  [G H : τ (Functor Y Z)]
  : τ (Functor
      (@Transf_cat Y Z G H)
      (@Transf_cat
        (Functor_cat X Y)
        (Functor_cat X Z)
        (@comp_cat_cov_func X Y Z G)
        (@comp_cat_cov_func X Y Z H)));

symbol comp_cat_cov_func_func_transf [X Y Z : Cat]
  [G H : τ (Functor Y Z)]
  (eta : τ (Transf G H))
  : τ (Transf
      (@comp_cat_cov_func X Y Z G)
      (@comp_cat_cov_func X Y Z H));

rule @fapp1_func _ _ (@comp_cat_cov_func_func $X $Y $Z) $G $H
  ↪ @comp_cat_cov_func_func_fapp1_func $X $Y $Z $G $H;

rule fapp0 (@comp_cat_cov_func_func_fapp1_func $X $Y $Z $G $H) $eta
  ↪ @comp_cat_cov_func_func_transf $X $Y $Z $G $H $eta;

rule @fapp1_fapp0 _ _ (@comp_cat_cov_func_func $X $Y $Z) $G $H $eta
  ↪ @comp_cat_cov_func_func_transf $X $Y $Z $G $H $eta;

/*
  Precomposition of transfors by a fixed functor.

  Mathematical notation:
    comp_cat_con_fapp1_func(F)
      : Transf(G,H) ⊢ Transf(G ∘ F,H ∘ F)

    comp_cat_con_transf(F,eta) = eta ∘ F
    comp_cat_con_transf(F,eta)[i] = eta[F[i]]

  Faithful surface syntax:
    eta : G => H
    eta ∘ F : G ∘ F => H ∘ F
*/
symbol comp_cat_con_fapp1_func [X Y Z : Cat]
  (F : τ (Functor X Y))
  [G H : τ (Functor Y Z)]
  : τ (Functor
      (@Transf_cat Y Z G H)
      (@Transf_cat
        X Z
        (@comp_cat_fapp0 X Y Z G F)
        (@comp_cat_fapp0 X Y Z H F)));

symbol comp_cat_con_transf [X Y Z : Cat]
  (F : τ (Functor X Y))
  [G H : τ (Functor Y Z)]
  (eta : τ (Transf G H))
  : τ (Transf
      (@comp_cat_fapp0 X Y Z G F)
      (@comp_cat_fapp0 X Y Z H F));

// Off-diagonal action of `comp_cat_cov_func_func_transf`. This is the
// horizontal composite `(H alpha) ∘ (eta F)`.
//
// Mathematical notation:
//   eta : G => H, alpha : F => K
//   comp_cat_cov_func_func_tapp1_fapp0(eta,alpha)
//     : G ∘ F => H ∘ K
//   comp_cat_cov_func_func_tapp1_fapp0(eta,alpha)
//     = (H alpha) ∘ (eta F).
symbol comp_cat_cov_func_func_tapp1_func [X Y Z : Cat]
  [G H : τ (Functor Y Z)]
  (eta : τ (Transf G H))
  [F K : τ (Functor X Y)]
  : τ (Functor
      (@Transf_cat X Y F K)
      (@Transf_cat
        X
        Z
        (@comp_cat_fapp0 X Y Z G F)
        (@comp_cat_fapp0 X Y Z H K)));

symbol comp_cat_cov_func_func_tapp1_fapp0 [X Y Z : Cat]
  [G H : τ (Functor Y Z)]
  (eta : τ (Transf G H))
  [F K : τ (Functor X Y)]
  (alpha : τ (Transf F K))
  : τ (Transf
      (@comp_cat_fapp0 X Y Z G F)
      (@comp_cat_fapp0 X Y Z H K))
≔ @comp_fapp0
    (Functor_cat X Z)
    (@comp_cat_fapp0 X Y Z G F)
    (@comp_cat_fapp0 X Y Z H F)
    (@comp_cat_fapp0 X Y Z H K)
    (@comp_cat_cov_transf X Y Z H F K alpha)
    (@comp_cat_con_transf X Y Z F G H eta);

rule @tapp0_fapp0
      _
      _
      _
      _
      $F
      (@comp_cat_cov_func_func_transf $X $Y $Z $G $H $eta)
  ↪ @comp_cat_con_transf $X $Y $Z $F $G $H $eta;

rule @tapp1_func
      _
      _
      _
      _
      $F
      $K
      (@comp_cat_cov_func_func_transf $X $Y $Z $G $H $eta)
  ↪ @comp_cat_cov_func_func_tapp1_func $X $Y $Z $G $H $eta $F $K;

rule fapp0
      (@comp_cat_cov_func_func_tapp1_func $X $Y $Z $G $H $eta $F $K)
      $alpha
  ↪ @comp_cat_cov_func_func_tapp1_fapp0 $X $Y $Z $G $H $eta $F $K $alpha;

rule @tapp1_fapp0
      _
      _
      _
      _
      $F
      $K
      (@comp_cat_cov_func_func_transf $X $Y $Z $G $H $eta)
      $alpha
  ↪ @comp_cat_cov_func_func_tapp1_fapp0 $X $Y $Z $G $H $eta $F $K $alpha;

rule @hom_precomp_fapp1_func Cat_cat $X $Y $Z $F $G $H
  ↪ @comp_cat_con_fapp1_func $X $Y $Z $F $G $H;

rule @hom_precomp_fapp1_fapp0 Cat_cat $X $Y $Z $F $G $H $eta
  ↪ @comp_cat_con_transf $X $Y $Z $F $G $H $eta;

rule @fapp1_func _ _ (@comp_cat_con_func $X $Y $Z $F) $G $H
  ↪ @comp_cat_con_fapp1_func $X $Y $Z $F $G $H;

rule fapp0 (@comp_cat_con_fapp1_func $X $Y $Z $F $G $H) $eta
  ↪ @comp_cat_con_transf $X $Y $Z $F $G $H $eta;

rule @fapp1_fapp0 _ _ (@comp_cat_con_func $X $Y $Z $F) $G $H $eta
  ↪ @comp_cat_con_transf $X $Y $Z $F $G $H $eta;

rule @tapp0_fapp0
      $X
      $Z
      _
      _
      $i
      (@comp_cat_con_transf $X $Y $Z $F $G $H $eta)
  ↪ @tapp0_fapp0
      $Y
      $Z
      $G
      $H
      (@fapp0 $X $Y $F $i)
      $eta;

rule @tapp1_func
      $X
      $Z
      _
      _
      $i
      $j
      (@comp_cat_con_transf $X $Y $Z $F $G $H $eta)
  ↪ @comp_cat_fapp0
      (Hom_cat $X $i $j)
      (Hom_cat $Y
        (@fapp0 $X $Y $F $i)
        (@fapp0 $X $Y $F $j))
      (Hom_cat $Z
        (@fapp0 $Y $Z $G (@fapp0 $X $Y $F $i))
        (@fapp0 $Y $Z $H (@fapp0 $X $Y $F $j)))
      (@tapp1_func
        $Y
        $Z
        $G
        $H
        (@fapp0 $X $Y $F $i)
        (@fapp0 $X $Y $F $j)
        $eta)
      (@fapp1_func $X $Y $F $i $j);

rule @tapp1_fapp0
      $X
      $Z
      _
      _
      $i
      $j
      (@comp_cat_con_transf $X $Y $Z $F $G $H $eta)
      $p
  ↪ @tapp1_fapp0
      $Y
      $Z
      $G
      $H
      (@fapp0 $X $Y $F $i)
      (@fapp0 $X $Y $F $j)
      $eta
      (@fapp1_fapp0 $X $Y $F $i $j $p);

rule sigma_Fst (@tapp1_fapp0 $X (Product_cat $A $B) $F $G $i $j $eta $p)
  ↪ @tapp1_fapp0 $X $A (sigma_Fst $F) (sigma_Fst $G) $i $j (sigma_Fst $eta) $p;

rule sigma_Snd (@tapp1_fapp0 $X (Product_cat $A $B) $F $G $i $j $eta $p)
  ↪ @tapp1_fapp0 $X $B (sigma_Snd $F) (sigma_Snd $G) $i $j (sigma_Snd $eta) $p;

rule @tapp1_fapp0 $A $B $F $F $X $Y (@id (Functor_cat $A $B) $F) $p
  ↪ @fapp1_fapp0 $A $B $F $X $Y $p;

// Strict naturality for off-diagonal ordinary transfor components, oriented as
// cut elimination.
//
// Surface/formula:
//   G[g] o epsilon[f] ↪ epsilon[g o f]
//   epsilon[f] o F[g] ↪ epsilon[f o g].
rule comp_fapp0
      (@fapp1_fapp0 $A $B $G $Y $Z $g)
      (@tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f)
  ↪ tapp1_fapp0 $ϵ (comp_fapp0 $g $f);

rule comp_fapp0
      (@tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f)
      (@fapp1_fapp0 $A $B $F $X0 $X $g)
  ↪ tapp1_fapp0 $ϵ (comp_fapp0 $f $g);

// Arrow-indexed component at an identity base arrow is definitionally usable as
// the ordinary diagonal component, without rewriting away the stable
// `tapp1_fapp0` head.
unif_rule @tapp1_fapp0 $A $B $F $G $X $X $ϵ (@id $A $X)
  ≡ @tapp0_fapp0 $A $B $F $G $X $ϵ
  ↪ [ tt ≡ tt ];

// Cat-valued object-level projections of strict naturality. Both composites
// fold to the off-diagonal component at the base arrow.
//
// Surface/formula:
//   D[p](eta[x](u)) ↪ eta[p](u)
//   eta[y](E[p](u)) ↪ eta[p](u).
//
// Keep the outer `fapp0` source/target categories implicit. The explicit
// arguments below are the stable ordinary action/component heads themselves,
// not reducible fibre-category expressions.
rule fapp0
      (@fapp1_fapp0 $K Cat_cat $D $x $y $p)
      (fapp0 (@tapp0_fapp0 $K Cat_cat $E $D $x $eta) $u)
  ↪ fapp0 (@tapp1_fapp0 $K Cat_cat $E $D $x $y $eta $p) $u;

rule fapp0
      (@tapp0_fapp0 $K Cat_cat $E $D $y $eta)
      (fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $p) $u)
  ↪ fapp0 (@tapp1_fapp0 $K Cat_cat $E $D $x $y $eta $p) $u;

/*
  Internalized product formation in Cat.

  Mathematical notation:
    Product_cat_func[A][B] = A x B
    Product_cat_fapp0_func(A)[B] = A x B

    Product_cat_fapp1_func(A,A')[G]
      = Product_cat_fapp1_fapp0_functord(G)
      : Product_cat_func[A] => Product_cat_func[A']

    Product_cat_fapp1_tapp0_func(G,B)
      = G * 1_B : A x B ⊢ A' x B

    (G * 1_B)[(x,y)] = (G[x],y)
    (G * 1_B)[(p,q)] = (G[p],q)

  Faithful surface syntax:
    A x B
    G * 1_B

  `Product_cat_fapp1_tapp0_func` is the stable fixed-right projection of the
  arrow-action of `Product_cat_func`. `Product_mapL_func_func` is only the
  defined functorial package G |-> G * 1_B.
*/
constant symbol Product_cat_func
  : τ (Functor Cat_cat (Functor_cat Cat_cat Cat_cat));

injective symbol Product_cat_fapp0_func (A : Cat)
  : τ (Functor Cat_cat Cat_cat);

rule @fapp0 _ _ Product_cat_func $A
  ↪ @Product_cat_fapp0_func $A;

rule @fapp0 Cat_cat Cat_cat (@Product_cat_fapp0_func $A) $B
  ↪ Product_cat $A $B;

symbol Product_cat_fapp1_func [A A' : Cat]
  : τ (Functor
      (Functor_cat A A')
      (Functord_cat
        (Product_cat_fapp0_func A)
        (Product_cat_fapp0_func A')));

symbol Product_cat_fapp1_fapp0_functord [A A' : Cat]
  (G : τ (Functor A A'))
  : τ (Functord
      (Product_cat_fapp0_func A)
      (Product_cat_fapp0_func A'));

symbol Product_cat_fapp1_tapp0_func [A A' B : Cat]
  (G : τ (Functor A A'))
  : τ (Functor (Product_cat A B) (Product_cat A' B));

rule @fapp1_func _ _ Product_cat_func $A $A'
  ↪ Product_cat_fapp1_func;

rule fapp0 (@Product_cat_fapp1_func $A $A') $G
  ↪ Product_cat_fapp1_fapp0_functord $G;

rule @fapp1_fapp0 _ _ Product_cat_func $A $A' $G
  ↪ Product_cat_fapp1_fapp0_functord $G;

rule @tapp0_fapp0
      Cat_cat
      Cat_cat
      (@Product_cat_fapp0_func $A)
      (@Product_cat_fapp0_func $A')
      $B
      (@Product_cat_fapp1_fapp0_functord $A $A' $G)
  ↪ Product_cat_fapp1_tapp0_func $G;

rule sigma_Fst (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
  ↪ comp_cat_fapp0 $G Product_projL_func;

rule sigma_Snd (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
  ↪ Product_projR_func;

rule @fapp0 _ _ (@Product_cat_fapp1_tapp0_func $A $A' $B $G) (Struct_sigma $x $y)
  ↪ Struct_sigma
      (fapp0 $G $x)
      $y;

rule @fapp1_func _ _ (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y')
  ↪ Struct_sigma
      (@comp_cat_fapp0
        (Product_cat
          (Hom_cat $A $x $x')
          (Hom_cat $B $y $y'))
        (Hom_cat $A $x $x')
        (Hom_cat $A'
          (@fapp0 $A $A' $G $x)
          (@fapp0 $A $A' $G $x'))
        (@fapp1_func $A $A' $G $x $x')
        (@Product_projL_func
          (Hom_cat $A $x $x')
          (Hom_cat $B $y $y')))
      (@Product_projR_func
        (Hom_cat $A $x $x')
        (Hom_cat $B $y $y'));

rule @fapp1_fapp0 _ _ (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y')
      (Struct_sigma $p $q)
  ↪ Struct_sigma
      (fapp1_fapp0 $G $p)
      $q;

// Defined functorial package for the fixed-right product action.
//
// Mathematical notation:
//   Product_mapL_func_func(A,A',B)[G] = G * 1_B.
//
// This is a readability alias through the `Product_cat_func` projection
// ladder, not an independent stable-head theory.
symbol Product_mapL_func_func [A A' B : Cat]
  : τ (Functor
      (Functor_cat A A')
      (Functor_cat (Product_cat A B) (Product_cat A' B)))
≔ @comp_cat_fapp0
    (Functor_cat A A')
    (@Functord_cat Cat_cat
      (@Product_cat_fapp0_func A)
      (@Product_cat_fapp0_func A'))
    (Functor_cat (Product_cat A B) (Product_cat A' B))
    (@tapp0_func
      Cat_cat
      Cat_cat
      (@Product_cat_fapp0_func A)
      (@Product_cat_fapp0_func A')
      B)
    (@Product_cat_fapp1_func A A');

/*
  Product evaluation: apply a functor to an object.

  Mathematical notation:
    Eval_func(A,B) : (A ⊢ B) x A ⊢ B
    Eval_func(A,B)[(F,x)] = F[x]

    Eval_fapp1_func(A,B,F,G,x,y)
      : (F => G) x Hom_A(x,y) ⊢ Hom_B(F[x],G[y])
    Eval_fapp1_func(A,B,F,G,x,y)[(eta,p)] = eta[p]

  Faithful surface syntax:
    F[x]
    eta[p]
*/
symbol Eval_func [A B : Cat]
  : τ (Functor (Product_cat (Functor_cat A B) A) B);

rule fapp0 (@Eval_func $A $B) (Struct_sigma $F $x)
  ↪ fapp0 $F $x;

symbol Eval_fapp1_func [A B : Cat]
  [F G : τ (Functor A B)]
  [x y : τ (Obj A)]
  : τ (Functor
      (Product_cat (Transf_cat F G) (Hom_cat A x y))
      (Hom_cat B (fapp0 F x) (fapp0 G y)));

rule @fapp1_func _ _ (@Eval_func $A $B) (Struct_sigma $F $x) (Struct_sigma $G $y)
  ↪ Eval_fapp1_func;

rule fapp0 (@Eval_fapp1_func $A $B $F $G $x $y) (Struct_sigma $eta $p)
  ↪ tapp1_fapp0 $eta $p;

rule @fapp1_fapp0 _ _ (@Eval_func $A $B)
      (Struct_sigma $F $x)
      (Struct_sigma $G $y)
      (Struct_sigma $eta $p)
  ↪ tapp1_fapp0 $eta $p;

/*
  Fixed-point section for evaluation.

  Mathematical notation:
    Eval_at_func(A,B,x) : (A ⊢ B) ⊢ (A ⊢ B) x A
    Eval_at_func(A,B,x)[F] = (F,x)
    Eval_func(A,B) o Eval_at_func(A,B,x) = fapp0_func(A,B,x)

  Faithful surface syntax:
    F |-> (F,x)
*/
symbol Eval_at_func [A B : Cat] (x : τ (Obj A))
  : τ (Functor
      (Functor_cat A B)
      (Product_cat (Functor_cat A B) A));

rule sigma_Fst (@Eval_at_func $A $B $x)
  ↪ @id_func (Functor_cat $A $B);

rule sigma_Snd (@Eval_at_func $A $B $x)
  ↪ Const_func $x;

rule @fapp0 (Functor_cat $A $B) (Product_cat (Functor_cat $A $B) $A)
      (@Eval_at_func $A $B $x) $F
  ↪ Struct_sigma $F $x;

rule @fapp1_func (Functor_cat $A $B) (Product_cat (Functor_cat $A $B) $A)
      (@Eval_at_func $A $B $x) $F $G
  ↪ Struct_sigma
      (@id_func (@Transf_cat $A $B $F $G))
      (@Const_func
        (@Transf_cat $A $B $F $G)
        (Hom_cat $A $x $x)
        (@id $A $x));

rule @fapp1_fapp0 (Functor_cat $A $B) (Product_cat (Functor_cat $A $B) $A)
      (@Eval_at_func $A $B $x) $F $G $eta
  ↪ Struct_sigma $eta (id $A $x);

rule @comp_cat_fapp0
      (Functor_cat $A $B)
      (Product_cat (Functor_cat $A $B) $A)
      $B
      (@Eval_func $A $B)
      (@Eval_at_func $A $B $x)
  ↪ fapp0_func $x;

/*
  Ordinary product curry/uncurry scaffold.

  Mathematical notation:
    curry_func_func(A,B,C)[F] = curry(F)
    curry(F)[x][y] = F[(x,y)]

    uncurry_func_func(A,B,C)[G] = uncurry(G)
    uncurry(G)[(x,y)] = G[x][y]
    uncurry(G)[(p,q)] = G[p][q]

  Faithful surface syntax:
    curry F
    uncurry G

  `curry_func_func` and `uncurry_func_func` are the primary semantic packages.
  `curry_func`, `curry_fapp0_func`, and `uncurry_func` are definitional
  projections. Full adjunction/coherence packaging remains future work.
*/
symbol curry_func_func [A B C : Cat]
  : τ (Functor
      (Functor_cat (Product_cat A B) C)
      (Functor_cat A (Functor_cat B C)))
≔ @comp_cat_fapp0
    (Functor_cat (Product_cat A B) C)
    (Functor_cat (Functor_cat B (Product_cat A B)) (Functor_cat B C))
    (Functor_cat A (Functor_cat B C))
    (@comp_cat_con_func
      A
      (Functor_cat B (Product_cat A B))
      (Functor_cat B C)
      (@Product_pair_tele_func A B))
    (@comp_cat_cov_func_func B (Product_cat A B) C);

symbol curry_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  : τ (Functor A (Functor_cat B C))
≔ fapp0 curry_func_func F;

symbol curry_fapp0_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  : τ (Functor B C)
≔ fapp0 (curry_func F) x;

symbol uncurry_func_func [A B C : Cat]
  : τ (Functor
      (Functor_cat A (Functor_cat B C))
      (Functor_cat (Product_cat A B) C))
≔ @comp_cat_fapp0
    (Functor_cat A (Functor_cat B C))
    (Functor_cat
      (Product_cat A B)
      (Product_cat (Functor_cat B C) B))
    (Functor_cat (Product_cat A B) C)
    (@comp_cat_cov_func
      (Product_cat A B)
      (Product_cat (Functor_cat B C) B)
      C
      (@Eval_func B C))
    (@Product_mapL_func_func A (Functor_cat B C) B);

symbol uncurry_func [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  : τ (Functor (Product_cat A B) C)
≔ fapp0 uncurry_func_func G;

// The transfor action of semantic uncurry depends on the higher arrow-action
// of `Product_cat_func` on a transfor `theta`. Keep it deferred rather than
// reinstating an independent `Product_mapL_transf` stable package.

/*
  More-internal ordinary hom-action.

  This ports the settled v2 core without also committing to the later
  hom-action packaging heads.  The functor sends a transfor ϵ : F => G to the
  internalized action

    hom_int(id_A) => hom_int(G) ∘ F^op.

  Surface/formula:
    tapp1_int_func_transf(F,G)[ϵ]
      : Hom_A(~,—) => Hom_B(F^op ~,G —)

    fapp1_int_transf(F)
      = tapp1_int_func_transf(F,F)[id_F]
*/
symbol tapp1_int_func_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  τ (Functor
      (Transf_cat F G)
      (Transf_cat
        (@hom_int A A (@id_func A))
        (comp_cat_fapp0
          (@hom_int B A G)
          (@Op_func A B F))));

// Object action of `tapp1_int_func_transf`.
symbol tapp1_int_fapp0_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (ϵ : τ (Transf F G)),
  τ (Transf
      (@hom_int A A (@id_func A))
      (comp_cat_fapp0
        (@hom_int B A G)
        (@Op_func A B F)));

rule fapp0 (@tapp1_int_func_transf $A $B $F $G) $ϵ
  ↪ @tapp1_int_fapp0_transf $A $B $F $G $ϵ;

// Hom action of `tapp1_int_func_transf`.
symbol tapp1_int_fapp1_func_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (ϵ ϵ' : τ (Transf F G)),
  τ (Functor
      (Hom_cat (Transf_cat F G) ϵ ϵ')
      (Hom_cat
        (Transf_cat
          (@hom_int A A (@id_func A))
          (comp_cat_fapp0
            (@hom_int B A G)
            (@Op_func A B F)))
        (@tapp1_int_fapp0_transf A B F G ϵ)
        (@tapp1_int_fapp0_transf A B F G ϵ')));

rule @fapp1_func _ _ (@tapp1_int_func_transf $A $B $F $G) $ϵ $ϵ'
  ↪ @tapp1_int_fapp1_func_transf $A $B $F $G $ϵ $ϵ';

// Identity-specialized ordinary internal hom-action.
symbol fapp1_int_transf : Π [A B : Cat], Π (F : τ (Functor A B)),
  τ (Transf
      (@hom_int A A (@id_func A))
      (comp_cat_fapp0
        (@hom_int B A F)
        (@Op_func A B F)));

rule @tapp1_int_fapp0_transf $A $B $F $F (id (Functor_cat $A $B) $F)
  ↪ @fapp1_int_transf $A $B $F;

// First projection of the identity-specialized ordinary internal hom-action at
// a fixed source object. This is the identity-specialized counterpart of
// `tapp1_at_transf`.
symbol fapp1_at_transf : Π [A B : Cat], Π (F : τ (Functor A B)),
  Π (X : τ (Obj A)),
  τ (Transf
      (@hom_ A A (@id_func A) X)
      (@hom_ B A F (@fapp0 A B F X)));

rule @tapp0_fapp0
      (Op_cat $A)
      (@Catd_cat $A)
      _
      _
      $X
      (@fapp1_int_transf $A $B $F)
  ↪ @fapp1_at_transf $A $B $F $X;

// First projection of the internal off-diagonal action at a fixed source
// object. This exposes the whole transfor
//   Hom_A(X,-) => Hom_B(F[X],G[-])
// before projecting again to the hom-functor component at Y.
symbol tapp1_at_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (X : τ (Obj A)),
  Π (ϵ : τ (Transf F G)),
  τ (Transf
      (@hom_ A A (@id_func A) X)
      (@hom_ B A G (@fapp0 A B F X)));

rule @tapp0_fapp0
      (Op_cat $A)
      (@Catd_cat $A)
      _
      _
      $X
      (@tapp1_int_fapp0_transf $A $B $F $G $ϵ)
  ↪ @tapp1_at_transf $A $B $F $G $X $ϵ;

rule @tapp1_at_transf $A $B $F $F $X (id (Functor_cat $A $B) $F)
  ↪ @fapp1_at_transf $A $B $F $X;

rule @tapp0_fapp0
      $A
      Cat_cat
      _
      _
      $Y
      (@tapp1_at_transf $A $B $F $G $X $ϵ)
  ↪ @tapp1_func $A $B $F $G $X $Y $ϵ;

rule @tapp0_fapp0
      $A
      Cat_cat
      _
      _
      $Y
      (@fapp1_at_transf $A $B $F $X)
  ↪ @fapp1_func $A $B $F $X $Y;

/*
  Ordinary internal hom-action package.

  Surface/formula:
    tapp1_int_func_transf(F,G)[epsilon]
      = internal action Hom_A(~,-) => Hom_B(F^op ~, G -)
    fapp1_int_transf(F) is the identity-specialized action.
*/

// -------------------------------------------------------------------------------------------------
// 6. Directed Cat-valued family constructors
// -------------------------------------------------------------------------------------------------

/*
  Mathematical notation:
    E[k]                      = Fibre_cat E k
    F^*E                      = Pullback_catd E F
    F^*E[a]                   = E[F[a]]
    Const_catd(K,A)[k]        = A
    Terminal_catd(K)          = Const_catd(K,Terminal_cat)
    Op_catd(E)[k]             = E[k]^op
    Pi_cat(E)                 = Π k :^n K, E[k]
                                = k :^n K ; 1[k] ⊢ E[k]
    piapp0(s,k)               = s[k]
*/
// Fixed-base notation: fibre of a directed family.
//
// Surface/formula:
//   E[k] = Fibre_cat(E,k)
symbol Fibre_cat [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) : Cat
≔ @fapp0 K Cat_cat E k;

// Fixed-base notation: reindex a displayed Cat-valued family along a functor.
//
// Surface/formula:
//   F^*E : A ⊢ Cat
//   (F^*E)[a] = E[F[a]]
symbol Pullback_catd [A B : Cat] (E : τ (Catd B)) (F : τ (Functor A B))
  : τ (Catd A)
≔ @comp_cat_fapp0 A B Cat_cat E F;

// Internalized-x prerequisite: generic base-arrow transport for displayed
// Cat-valued families.
//
// Surface/formula:
//   E[p] : E[x] ⊢ E[y]
//   catd_transport_func(E,p) = fapp1_fapp0(E,p)
symbol catd_transport_func [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat E y))
≔ @fapp1_fapp0 K Cat_cat E x y p;

// Strict object transport, oriented as cut elimination.
//
// Surface/formula:
//   E[q](E[p](u)) ↪ E[q o p](u).
//
// Keep the outer `fapp0` source/target categories implicit. The explicit
// arguments below are the stable functor-action heads themselves, not reducible
// fibre-category expressions.
rule fapp0
      (@fapp1_fapp0 $K Cat_cat $E $y $z $q)
      (fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $p) $u)
  ↪ fapp0
      (@fapp1_fapp0
        $K
        Cat_cat
        $E
        $x
        $z
        (@comp_fapp0 $K $x $y $z $q $p))
      $u;

// Internalized-x prerequisite: functorial package for pullback/reindexing of
// directed families along a base functor.
//
// Surface/formula:
//   Pullback_catd_func(F) : (B ⊢ Cat) ⊢ (A ⊢ Cat)
//   Pullback_catd_func(F)[E] = F^*E
//
// The general `Pullback_catd` remains a composition definition; this package
// is the stable functor-level action needed by internalized base-varying
// constructors such as Pi.
injective symbol Pullback_catd_func [A B : Cat]
  (F : τ (Functor A B))
  : τ (Functor (Catd_cat B) (Catd_cat A));

rule @fapp0 (@Catd_cat $B) (@Catd_cat $A)
      (@Pullback_catd_func $A $B $F) $E
  ↪ @Pullback_catd $A $B $E $F;

// Arrow action of the internalized Catd constructor. `Catd_cat_func` is a
// definition, so the rule matches the canonical unfolded composition head.
rule @fapp1_fapp0
      (Op_cat Cat_cat)
      Cat_cat
      (@comp_cat_fapp0
        (Op_cat Cat_cat)
        (Catd_cat Cat_cat)
        Cat_cat
        (@fapp0_func Cat_cat Cat_cat Cat_cat)
        Functor_cat_func)
      $B
      $A
      $F
  ↪ @Pullback_catd_func $A $B $F;

// Pointwise projection for the hom-action of family pullback.
rule @tapp0_fapp0
      $A
      Cat_cat
      _
      _
      $a
      (@fapp1_fapp0
        (@Catd_cat $B)
        (@Catd_cat $A)
        (@Pullback_catd_func $A $B $F)
        $E
        $D
        $η)
  ↪ @tapp0_fapp0
      $B
      Cat_cat
      $E
      $D
      (@fapp0 $A $B $F $a)
      $η;

// Fixed-base layer: constant Cat-valued family.
//
// Surface/formula:
//   const_K(A)[k] = A.
injective symbol Const_catd (K : Cat) (A : Cat) : τ (Catd K);

rule @fapp0 $K Cat_cat (@Const_catd $K $A) $_ ↪ $A;
rule @comp_cat_fapp0 $A $B Cat_cat (@Const_catd $B $C) $F
  ↪ @Const_catd $A $C;
rule @hom_ $A $B (@Const_func $B $A $u) $w
  ↪ @Const_catd $B (Hom_cat $A $w $u);

rule @fapp1_func $K Cat_cat (@Const_catd $K $A) $x $y
  ↪ @Const_func
      (Hom_cat $K $x $y)
      (Functor_cat $A $A)
      (@id_func $A);

rule @fapp1_fapp0 $K Cat_cat (@Const_catd $K $A) $x $y $_ ↪ @id_func $A;

// Fixed-base layer: terminal displayed family.
//
// Surface/formula:
//   Terminal_catd(K) = 1_K = const_K(1).
symbol Terminal_catd (K : Cat) : τ (Catd K)
≔ @Const_catd K Terminal_cat;

// Fixed-base layer: pointwise opposite of a directed family.
//
// Surface/formula:
//   Op_catd(E)[k] = E[k]^op.
injective symbol Op_catd [K : Cat] (E : τ (Catd K)) : τ (Catd K);

rule @fapp0 (@Catd_cat $K) (@Catd_cat $K) (@Op_catd_func $K) $E
  ↪ @Op_catd $K $E;

rule @comp_cat_fapp0 $K Cat_cat Cat_cat op $E
  ↪ @Op_catd $K $E;

rule @fapp0 $K Cat_cat (@Op_catd $K $E) $k
  ↪ Op_cat (@fapp0 $K Cat_cat $E $k);

rule @Op_catd $K (@Op_catd $K $E) ↪ $E;
rule @Op_catd $K (@Const_catd $K $A) ↪ @Const_catd $K (Op_cat $A);

// Fixed-base layer: pointwise opposite of a displayed functor.
//
// Surface/formula:
//   Op_funcd(FF)[k] = Op_func(FF[k]).
injective symbol Op_funcd [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : τ (Functord (Op_catd E) (Op_catd D));

rule @Op_funcd $K (@Op_catd $K $E) (@Op_catd $K $D) (@Op_funcd $K $E $D $FF)
  ↪ $FF;

rule @Op_funcd $K $E $E (@id_funcd $K $E)
  ↪ @id_funcd $K (@Op_catd $K $E);

// Pointwise projection of displayed opposite. The source/target family slots
// are deliberately implicit; the explicit `Op_funcd` argument is the
// discriminator.
rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $x
      (@Op_funcd $K $E $D $FF)
  ↪ @Op_func
      (Fibre_cat $E $x)
      (Fibre_cat $D $x)
      (@tapp0_fapp0 $K Cat_cat $E $D $x $FF);

// Pointwise projection of displayed composition. This belongs with the
// displayed-functor calculus: at each base object x, the composite displayed
// functor projects to the ordinary composite of fibre functors.
rule @tapp0_fapp0
      $K Cat_cat $E $C $x
      (@comp_catd_fapp0 $K $E $D $C $FF $GG)
  ↪ @comp_cat_fapp0
      (Fibre_cat $E $x)
      (Fibre_cat $D $x)
      (Fibre_cat $C $x)
      (@tapp0_fapp0 $K Cat_cat $D $C $x $FF)
      (@tapp0_fapp0 $K Cat_cat $E $D $x $GG);

// Fixed-base layer: section category of a displayed family.
//
// Surface/formula:
//   Pi_cat(E) = Π k :^n K, E[k]
//             = k :^n K ; 1[k] ⊢ E[k]
//   section object s has components s[k] : E[k].
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;

rule @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ↪ Functor_cat $K $A;

// Fixed-base layer: functorial section-category constructor at a fixed base.
//
// Surface/formula:
//   Pi_func(K)[E] = Π k :^n K, E[k].
//                 = k :^n K ; 1[k] ⊢ E[k].
injective symbol Pi_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
rule @fapp0 (@Catd_cat $K) Cat_cat (@Pi_func $K) $E
  ↪ @Pi_cat $K $E;

// Stable displayed-identity bridge for Pi. Generic strict functoriality
// catches `Pi_func(K)[id]`, while this development often keeps the displayed
// identity visible as `id_funcd`; this rule is the same identity preservation
// computation at that stable head.
rule @fapp1_fapp0
      (@Catd_cat $K)
      Cat_cat
      (@Pi_func $K)
      $E
      $E
      (@id_funcd $K $E)
  ↪ @id_func (@Pi_cat $K $E);

// Internalized-x layer: global natural package for Pi over varying bases.
//
// Surface/formula:
//   Pi_int_funcd : K :^n Cat^op ; (K ⊢ Cat) ⊢ Cat
//   Pi_int_funcd[K] = Pi_func(K)
//
// The base is Op(Cat) because section categories pull back contravariantly
// along functors.
constant symbol Pi_int_funcd
  : τ (Functord
      Catd_cat_func
      (@Const_catd (Op_cat Cat_cat) Cat_cat));

rule @tapp0_fapp0
      (Op_cat Cat_cat)
      Cat_cat
      _
      _
      $K
      Pi_int_funcd
  ↪ @Pi_func $K;

// Internalized-x layer: stable normal form for pulling the internal Pi package
// back along a Cat-valued contravariant base functor.
//
// Surface/formula:
//   for G : K ⊢ Cat^op,
//   Pi_pullback_funcd(G) : x :^n K ; (G[x] ⊢ Cat) ⊢ Cat
//   Pi_pullback_funcd(G)[x] = Pi_func(G[x])
//   Sigma_catd_transport_func(Pi_pullback_funcd(G),p,E)
//     = section_pullback_func(G[p],E)
//
// The fold rule routes the semantic `Pi_int_funcd`/`Pullback_catd_func`
// expression into this head while keeping the reducible endpoint family slots
// implicit on the LHS.
injective symbol Pi_pullback_funcd [K : Cat]
  (G : τ (Functor K (Op_cat Cat_cat)))
  : τ (Functord
      (@comp_cat_fapp0 K (Op_cat Cat_cat) Cat_cat Catd_cat_func G)
      (@Const_catd K Cat_cat));

rule @fapp1_fapp0
      (@Catd_cat (Op_cat Cat_cat))
      (@Catd_cat $K)
      (@Pullback_catd_func $K (Op_cat Cat_cat) $G)
      _
      _
      Pi_int_funcd
  ↪ @Pi_pullback_funcd $K $G;

rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $x
      (@Pi_pullback_funcd $K $G)
  ↪ @Pi_func (@fapp0 $K (Op_cat Cat_cat) $G $x);

// Fixed-base layer: functorial section evaluation at k.
//
// Surface/formula:
//   piapp0_func(E,k) : (Π i :^n K, E[i]) ⊢ E[k].
symbol piapp0_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Pi_cat E) (Fibre_cat E k))
≔ comp_cat_fapp0
     (@fapp0_func Terminal_cat (Fibre_cat E k) Terminal_obj)
     (@tapp0_func K Cat_cat (@Const_catd K Terminal_cat) E k);

// Fixed-base layer: section object evaluation.
//
// Surface/formula:
//   piapp0(s,k) = s[k] : E[k].
symbol piapp0 : Π [K : Cat], Π [E : τ (Catd K)],
  Π (s : τ (Obj (Pi_cat E))),
  Π (k : τ (Obj K)),
  τ (Obj (Fibre_cat E k))
≔ λ K E s k, @fapp0 (Pi_cat E) (Fibre_cat E k) (@piapp0_func K E k) s;

// Fixed-base covariant transport from a fibre object.
//
// Surface/formula:
//   fib_cov_tapp0_func(E,x,u,y) : Hom_K(x,y) ⊢ E[y]
//   fib_cov_tapp0_func(E,x,u,y)[f] = E[f](u).
symbol fib_cov_tapp0_func [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Functor (Hom_cat K x y) (Fibre_cat E y))
≔ comp_cat_fapp0
     (@fapp0_func (Fibre_cat E x) (Fibre_cat E y) u)
     (@fapp1_func K Cat_cat E x y);

// General endpoint notation for dependent homs along a displayed functor. The
// old one-family endpoint is the identity-family specialization.
//
// Surface/formula:
//   homd_(FF,x,u,y,v)[f : x ->^Z y]
//     = Hom_{E[y]}(FF[y](v), E[f](u)).
injective symbol homd_ [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  (v : τ (Obj (Fibre_cat D y)))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat)
≔ @hom_con
     (Fibre_cat E y)
     (fapp0
       (@tapp0_fapp0 Z Cat_cat D E y FF)
       v)
     (Hom_cat Z x y)
     (@fib_cov_tapp0_func Z E x y u);

// Fibre transport is introduced later as a defined projection from the
// reordered functor `fib_cov_tapp0_func`. v3.2 deliberately avoids the v3.1
// generic strict identity/composition transport rewrites for arbitrary
// Cat-valued families.

// -------------------------------------------------------------------------------------------------
// 7. Directed Sigma categories and maps between totals
// -------------------------------------------------------------------------------------------------

// Sigma totalization is a stable constructor package. Its map/projection heads
// are injective in the syntactic kernel sense: equality of these packaged
// constructors may recover their displayed-family data.
/*
  Mathematical notation:
    Sigma_cat(E)              = Σ k :^n K, E[k]
    Obj(Sigma_cat(E))         = Σ (k : Obj K), Obj(E[k])
    Sigma_proj1_func(E)(k,u)  = k
    Sigma_proj1_pullback(R,D) = D pulled back along Sigma_proj1_func(R)
    Π (k,r) :^n ΣR, D[k]      = Functord_cat(R,D)
    Sigma_func[K][E]          = Sigma_cat(E)
    sigma_map_func(η)(k,u)    = (k, η_k(u))
*/
// Fixed-base layer: total category of a directed family.
//
// Surface/formula:
//   Sigma_cat(E) = Σ k :^n K, E[k]
//   Obj(Sigma_cat(E)) has objects (k,u).
//
// Current computational status:
//   The Sigma rules below expose object action, capped 1-arrow action
//   (`fapp1_fapp0`), fixed-endpoint hom-action (`fapp1_func`), and 1-arrow
//   composition. They are deliberately enough for path/arrow transitivity,
//   total transports, rho coherence, and the current Sigma-map hom-action
//   package. Higher hom-action data can still be refined as the omega layer
//   grows.
injective symbol Sigma_cat [K : Cat] (E : τ (Catd K)) : Cat;

// Non-dependent Sigma is ordinary product. This must reduce before the generic
// dependent `Hom(Sigma)` presentation, so constant-family totals inherit the
// pointwise Product normal forms directly.
rule @Sigma_cat $K (@Const_catd $K $A)
  ↪ Product_cat $K $A;

// Fixed-base layer: functorial total-category constructor.
//
// Surface/formula:
//   Sigma_func(K)[E] = Sigma_cat(E).
injective symbol Sigma_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
rule @fapp0 (@Catd_cat $K) Cat_cat (@Sigma_func $K) $E
  ↪ @Sigma_cat $K $E;

rule τ (Obj (@Sigma_cat $K $E))
  ↪ `τΣ_ k : τ (Obj $K), Obj (Fibre_cat $E k);

// Hom categories of Sigma totals are the dependent-hom Sigma over base arrows.
//
// Surface/formula:
//   Hom_{Sigma E}((x,u),(y,v))
//     = Sigma (p : Hom_K(x,y)), Hom_{E[y]}(E[p](u),v).
rule Hom_cat (@Sigma_cat $K $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_cat
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (@homd_ $K $E $E (@id_funcd $K $E) $x $u $y $v));

// Constructor for arrows in a Sigma category, using the Sigma-hom
// characterization above. The explicit fibre arrow is the second component of
// the encoded dependent pair in the reduced hom category.
symbol sigma_arrow [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Hom
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u)
      v))
  : τ (Hom
      (@Sigma_cat K E)
      (Struct_sigma x u)
      (Struct_sigma y v))
≔ @Struct_sigma
    (Obj (Op_cat (Hom_cat K x y)))
    (λ f : τ (Obj (Op_cat (Hom_cat K x y))),
      Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) f))
    p
    alpha;

// Composition of Sigma arrows.
//
// Surface/formula:
//   (q,beta) o (p,alpha)
//     = (q o p, beta o E[q](alpha)).
//
// The source of E[q](alpha) computes from E[q](E[p](u)) to
// E[q o p](u) by strict object transport. The LHS matches the reduced
// Sigma-hom pair form; the Sigma category itself is the discriminator needed to
// recover K and E.
rule @comp_fapp0
      (@Sigma_cat $K $E)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
      (Struct_sigma $z $w)
      (Struct_sigma $q $beta)
      (Struct_sigma $p $alpha)
  ↪ @sigma_arrow
      $K
      $E
      $x
      $z
      $u
      $w
      (@comp_fapp0 $K $x $y $z $q $p)
      (@comp_fapp0
        (Fibre_cat $E $z)
        (@fapp0
          (Fibre_cat $E $x)
          (Fibre_cat $E $z)
          (@catd_transport_func
            $K
            $E
            $x
            $z
            (@comp_fapp0 $K $x $y $z $q $p))
          $u)
        (@fapp0
          (Fibre_cat $E $y)
          (Fibre_cat $E $z)
          (@catd_transport_func $K $E $y $z $q)
          $v)
        $w
        $beta
        (@fapp1_fapp0
          (Fibre_cat $E $y)
          (Fibre_cat $E $z)
          (@catd_transport_func $K $E $y $z $q)
          (@fapp0
            (Fibre_cat $E $x)
            (Fibre_cat $E $y)
            (@catd_transport_func $K $E $x $y $p)
            $u)
          $v
          $alpha));

// Fixed-base layer: first projection from a total category.
//
// Surface/formula:
//   Sigma_proj1_func(E) : Sigma_cat(E) ⊢ K
//   Sigma_proj1_func(E)[(k,u)] = k.
injective symbol Sigma_proj1_func [K : Cat] (E : τ (Catd K))
  : τ (Functor (Sigma_cat E) K);

rule fapp0 (Sigma_proj1_func $E) (Struct_sigma $k $u) ↪ $k;

// Stable head for the computationally important projection pullback. General
// `Pullback_catd` stays a definition by composition, but this special case is
// discriminable so sections over the total category can contract to displayed
// functors out of the displayed family.
injective symbol Sigma_proj1_pullback_catd [K : Cat]
  (R D : τ (Catd K))
  : τ (Catd (@Sigma_cat K R));

rule @comp_cat_fapp0
      (@Sigma_cat $K $R)
      $K
      Cat_cat
      $D
      (@Sigma_proj1_func $K $R)
  ↪ @Sigma_proj1_pullback_catd $K $R $D;

rule @fapp0
      (@Sigma_cat $K $R)
      Cat_cat
      (@Sigma_proj1_pullback_catd $K $R $D)
      (Struct_sigma $k $r)
  ↪ @Fibre_cat $K $D $k;

rule @Functord_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
  ↪ @Functord_cat $K $R $D;

// Fixed-base layer: total map induced by a displayed functor.
//
// Surface/formula:
//   sigma_map_func(η) : Sigma_cat(E) ⊢ Sigma_cat(D)
//   sigma_map_func(η)[(k,u)] = (k,η[k](u)).
injective symbol sigma_map_func [K : Cat] [E D : τ (Catd K)]
  (η : τ (Functord E D))
  : τ (Functor (Sigma_cat E) (Sigma_cat D));

rule @fapp1_fapp0 (@Catd_cat $K) Cat_cat (@Sigma_func $K) $E $D $η
  ↪ @sigma_map_func $K $E $D $η;

rule @fapp0 _ _
      (@sigma_map_func $K $E $D $η)
      (Struct_sigma $k $u)
  ↪ Struct_sigma
      $k
      (fapp0 (@tapp0_fapp0 $K Cat_cat $E $D $k $η) $u);

rule @comp_cat_fapp0 _ _ _
      (@Sigma_proj1_func $K $D)
      (@sigma_map_func $K $E $D $η)
  ↪ @Sigma_proj1_func $K $E;

// Internalized-x prerequisite: canonical total arrow over a base arrow.
//
// Surface/formula:
//   sigma_transport_arrow(E,p,u) : (x,u) ->^Sigma_cat(E) (y,E[p](u))
//   in Sigma_cat(E) = Σ k :^n K, E[k].
// Canonical total arrow over a base arrow, defined by the smaller Sigma-arrow
// constructor pairing the base arrow with the identity fibre arrow at the
// transported endpoint.
symbol sigma_transport_arrow [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (@Sigma_cat K E)
      (Struct_sigma x u)
      (Struct_sigma y
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat E y)
          (@catd_transport_func K E x y p)
          u)))
≔ @sigma_arrow
    K
    E
    x
    y
    u
    (@fapp0
      (Fibre_cat E x)
      (Fibre_cat E y)
      (@catd_transport_func K E x y p)
      u)
    p
    (@id
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u));

// Generic action of a Sigma map on a canonical total transport arrow. This is a
// transparent alias for the ordinary functor action on the canonical total
// arrow.
symbol sigma_map_transport_arrow [K : Cat] [E D : τ (Catd K)]
  (η : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (@Sigma_cat K D)
      (Struct_sigma x
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@tapp0_fapp0 K Cat_cat E D x η)
          u))
      (Struct_sigma y
        (@fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          (@fapp0
            (Fibre_cat E x)
            (Fibre_cat E y)
            (@catd_transport_func K E x y p)
            u))))
≔ @fapp1_fapp0
    (@Sigma_cat K E)
    (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma x u)
    (Struct_sigma y
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
	    (@catd_transport_func K E x y p)
	    u))
    (@sigma_transport_arrow K E x y p u);

// Internalized-x prerequisite: Cat-valued family over a total category induced
// by a displayed functor into the constant category universe.
//
// Surface/formula:
//   if FF : k :^n K ; R[k] ⊢ Cat, then
//   Sigma_catd_functord_catd(FF) : (Σ k :^n K, R[k]) ⊢ Cat
//   Sigma_catd_functord_catd(FF)[(k,r)] = FF[k][r].
symbol Sigma_catd_functord_catd [K : Cat] [R : τ (Catd K)]
  (FF : τ (Functord R (@Const_catd K Cat_cat)))
  : τ (Catd (@Sigma_cat K R));

rule @fapp0
      (@Sigma_cat $K $R)
      Cat_cat
      (@Sigma_catd_functord_catd $K $R $FF)
      (Struct_sigma $k $r)
  ↪ @fapp0
      (Fibre_cat $R $k)
      Cat_cat
      (@tapp0_fapp0 $K Cat_cat $R (@Const_catd $K Cat_cat) $k $FF)
      $r;

// Internalized-x prerequisite: stable action of a Sigma-induced Cat-valued
// family along the canonical total transport arrow.
//
// Surface/formula:
//   Sigma_catd_transport_func(FF,p,r)
//     : FF[x][r] ⊢ FF[y][R[p](r)]
//   (Sigma_catd_functord_catd(FF))[sigma_transport_arrow(R,p,r)]
//     = Sigma_catd_transport_func(FF,p,r).
//
symbol Sigma_catd_transport_func [K : Cat] [R : τ (Catd K)]
  (FF : τ (Functord R (@Const_catd K Cat_cat)))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (r : τ (Obj (Fibre_cat R x)))
  : τ (Functor
      (Fibre_cat (@Sigma_catd_functord_catd K R FF) (Struct_sigma x r))
      (Fibre_cat
        (@Sigma_catd_functord_catd K R FF)
        (Struct_sigma y
          (@fapp0
            (Fibre_cat R x)
            (Fibre_cat R y)
            (@catd_transport_func K R x y p)
            r))))
≔ @fapp1_fapp0
    (@Sigma_cat K R)
    Cat_cat
    (@Sigma_catd_functord_catd K R FF)
    (Struct_sigma x r)
    (Struct_sigma y
      (@fapp0
        (Fibre_cat R x)
        (Fibre_cat R y)
        (@catd_transport_func K R x y p)
        r))
    (@sigma_transport_arrow K R x y p r);

// Generic uncurrying of a displayed transfor over a telescope into a displayed
// functor over the Sigma-total category.
//
// Surface/formula:
//   Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r].
//
// The object-component projection rule is installed later, after the generic
// displayed-transfor component head `tdapp0_fapp0` is declared.
constant symbol Sigma_transfd_funcd [K : Cat] [R : τ (Catd K)]
  [S T : τ (Functord R (@Const_catd K Cat_cat))]
  (eta : τ (Transfd S T))
  : τ (Functord
      (@Sigma_catd_functord_catd K R S)
      (@Sigma_catd_functord_catd K R T));

// -------------------------------------------------------------------------------------------------
// 8. Mixed-variance family functor
// -------------------------------------------------------------------------------------------------

/*
  These mixed-variance heads are stable syntactic constructors.  Their
  injectivity is a kernel contract used by unification, not a claim that the
  corresponding categorical data are invariantly recoverable up to equivalence.
  The `_func` suffix is reserved for functor-valued constructor packages.

  Surface/formula:
    Functor_catd(M,N)[k]       = M[k^-] ⊢_[k] N[k]
    Functor_catd_func(K)[M][N] = Functor_catd(M,N)
    Hom_catd(E,X,Y)[k]         = X[k^-] ->_[k]^E Y[k]
    Transf_catd(M,N,FF,GG)[k]  = FF[k^-] =>_[k] GG[k]
*/

injective symbol Functor_catd [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B : τ (Catd K))
  : τ (Catd K);

rule @fapp0 $K Cat_cat (@Functor_catd $K $A $B) $k
  ↪ Functor_cat (Fibre_cat $A $k) (Fibre_cat $B $k);

// Internalized constructor package for mixed-variance functor families.
injective symbol Functor_catd_func (K : Cat)
  : τ (Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Functor_cat (Catd_cat K) (Catd_cat K)));

// Partial application of `Functor_catd_func`.
injective symbol Functor_catd_fapp0_func [K : Cat]
  (A : τ (Catd (Op_cat K)))
  : τ (Functor (Catd_cat K) (Catd_cat K));

rule @fapp0 _ _
      (@Functor_catd_func $K) $A
  ↪ @Functor_catd_fapp0_func $K $A;

rule @fapp0 _ _ (@Functor_catd_fapp0_func $K $A) $B
  ↪ @Functor_catd $K $A $B;

// Mixed-variance hom family for two sections of a displayed family.
//
// Surface/formula:
//   Hom_catd(E,X,Y)[k] = X[k^-] ->_[k]^E Y[k].
injective symbol Hom_catd [K : Cat]
  (E : τ (Catd K))
  (X : τ (Obj (Pi_cat (Op_catd E))))
  (Y : τ (Obj (Pi_cat E)))
  : τ (Catd K);

rule @fapp0 $K Cat_cat (@Hom_catd $K $E $X $Y) $k
  ↪ Hom_cat
      (Fibre_cat $E $k)
      (@piapp0 $K (@Op_catd $K $E) $X $k)
      (@piapp0 $K $E $Y $k);

// Mixed-variance transfor family for two displayed functors.
//
// Surface/formula:
//   Transf_catd(M,N,FF,GG)[k] = FF[k^-] =>_[k] GG[k].
//
// Since `Transf_catd(M,N,FF,GG)` is already a Cat-valued family, sections of
// mixed-variance transfors are expressed by `Pi_cat (Transf_catd M N FF GG)`.
// No extra `Pid_cat` alias is needed unless a later computation requires a
// dedicated stable head for that shape.
injective symbol Transf_catd [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B : τ (Catd K))
  (FF : τ (Obj (Pi_cat (Op_catd (Functor_catd A B)))))
  (GG : τ (Obj (Pi_cat (Functor_catd A B))))
  : τ (Catd K);

rule @fapp0 $K Cat_cat (@Transf_catd $K $A $B $FF $GG) $k
  ↪ Transf_cat
      (@piapp0 $K (@Op_catd $K (@Functor_catd $K $A $B)) $FF $k)
      (@piapp0 $K (@Functor_catd $K $A $B) $GG $k);

rule @Hom_catd $K (@Const_catd $K Cat_cat) $X $Y
  ↪ @Functor_catd $K (@Op_func $K (Op_cat Cat_cat) $X) $Y;

rule @Hom_catd $K (@Functor_catd $K $A $B) $FF $GG
  ↪ @Transf_catd $K $A $B $FF $GG;

// -------------------------------------------------------------------------------------------------
// 9. Internal edge and presheaf-family classifiers
// -------------------------------------------------------------------------------------------------

// These named classifiers are defined composition pipelines.  Keep them named
// for readability, but do not use them as primitive discriminators unless a
// later rule genuinely requires that stronger unification contract.
/*
  Mathematical notation:
    Rep_Z(x)[y]               = Hom_Z(x,y)
    PathOut_Z(x)              = Σ_y Hom_Z(x,y)
    Edge_Z(x)[y]              = Hom_Z(x,y)^op
    Presheaf_catd(K)(A)[k]    = Functor_cat(A[k],Cat)
    HomPresheaf_Z(x)[y]       = Functor_cat(Hom_Z(x,y)^op,Cat)
*/

symbol Rep_catd_func [Z : Cat]
  : τ (Functor (Op_cat Z) (Catd_cat Z))
≔ @hom_int Z Z (@id_func Z);

// Fixed-source representable family.
//
// Surface/formula:
//   Rep_Z(x)[y] = Hom_Z(x,y).
symbol Rep_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd Z)
≔ @fapp0 (Op_cat Z) (Catd_cat Z) (@Rep_catd_func Z) x;

// Stable representable transport/precomposition head.
//
// Mathematical notation:
//   Rep_transport(p) : Rep_Z(y) ⊢ Rep_Z(x)
//   Rep_transport(p)[z][q] = q o p.
//
// Faithful surface syntax:
//   (q : y ->^Z z) |-> q o p.
injective symbol Rep_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functord (@Rep_catd Z y) (@Rep_catd Z x));

rule @fapp1_fapp0
      (Op_cat $Z)
      (@Catd_cat $Z)
      (@hom_int $Z $Z (@id_func $Z))
      $y
      $x
      $p
  ↪ @Rep_transport_func $Z $x $y $p;

rule @tapp0_fapp0
      $Z
      Cat_cat
      _
      _
      $z
      (@Rep_transport_func $Z $x $y $p)
  ↪ @hom_precomp_func $Z $x $y $z $p;

// Fixed-x layer: outgoing-path category at a fixed source object.
//
// Surface/formula:
//   PathOut_Z(x) = Σ y :^n Z, Hom_Z(x,y)
//   object notation: (y,p) with p : Hom_Z(x,y).
symbol PathOut_cat [Z : Cat] (x : τ (Obj Z)) : Cat
≔ @Sigma_cat Z (@Rep_catd Z x);

// Internalized-x layer: PathOut as a contravariant functor of the source.
//
// Surface/formula:
//   PathOut_cat_func(Z) : Z^op ⊢ Cat
//   PathOut_cat_func(Z)[x] = PathOut_Z(x)
//   PathOut_cat_func(Z)[p : x ->^Z y] : PathOut_Z(y) ⊢ PathOut_Z(x).
symbol PathOut_cat_func [Z : Cat]
  : τ (Functor (Op_cat Z) Cat_cat)
≔ @comp_cat_fapp0
     (Op_cat Z)
     (@Catd_cat Z)
     Cat_cat
     (@Sigma_func Z)
     (@Rep_catd_func Z);

// Internalized-x layer: readable name for PathOut's action on a base arrow.
//
// Surface/formula:
//   PathOut_transport_func(p) = PathOut_cat_func(Z)[p]
//   : PathOut_Z(y) ⊢ PathOut_Z(x)
//   and PathOut_transport_func(p)[(y,id_y)] = (y,p).
symbol PathOut_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functor (@PathOut_cat Z y) (@PathOut_cat Z x))
≔ @fapp1_fapp0
    (Op_cat Z)
    Cat_cat
    (@PathOut_cat_func Z)
    y
    x
    p;

// Internalized-x layer: family of motive categories over source objects.
//
// Surface/formula:
//   PathOutMotives_Z[x] = Catd(PathOut_Z(x))
//   i.e. a fibre object E is a motive E : PathOut_Z(x) ⊢ Cat.
symbol PathOutMotives_catd [Z : Cat]
  : τ (Catd Z)
≔ @comp_cat_fapp0
     Z
     (Op_cat Cat_cat)
     Cat_cat
     Catd_cat_func
     (@Op_func (Op_cat Z) Cat_cat (@PathOut_cat_func Z));

// Internalized-x target layer: Pi over the moving PathOut category.
//
// Surface/formula:
//   PathOutPi_Z : x :^n Z ; Catd(PathOut_Z(x)) ⊢ Cat
//   PathOutPi_Z[x][E] = Π q :^n PathOut_Z(x), E[q].
//
// This is deliberately the semantic pullback of `Pi_int_funcd` along
// `Op_func(PathOut_cat_func Z)`, then folded to `Pi_pullback_funcd`.
symbol PathOutPi_funcd [Z : Cat]
  : τ (Functord (@PathOutMotives_catd Z) (@Const_catd Z Cat_cat))
≔ @fapp1_fapp0
    (@Catd_cat (Op_cat Cat_cat))
    (@Catd_cat Z)
    (@Pullback_catd_func
      Z
      (Op_cat Cat_cat)
      (@Op_func (Op_cat Z) Cat_cat (@PathOut_cat_func Z)))
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    Pi_int_funcd;

// Internalized-x target layer: total target family for path induction.
//
// Surface/formula:
//   PathIndTgt_Z[(x,E)] = Π q :^n PathOut_Z(x), E[q]
//   over Σ x :^n Z, Catd(PathOut_Z(x)).
symbol PathIndTgt_catd [Z : Cat]
  : τ (Catd (@Sigma_cat Z (@PathOutMotives_catd Z)))
≔ @Sigma_catd_functord_catd
    Z
    (@PathOutMotives_catd Z)
    (@PathOutPi_funcd Z);

// Fixed-x notation: object `(y,p)` of PathOut_Z(x).
//
// Surface/formula:
//   pathout_obj(x;y,p) = (y,p).
symbol pathout_obj [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y))
  : τ (Obj (@PathOut_cat Z x))
≔ Struct_sigma y p;

// Fixed-x notation: distinguished reflexive outgoing path.
//
// Surface/formula:
//   reflout_x = (x,id_x) : PathOut_Z(x).
symbol pathout_refl_obj [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (@PathOut_cat Z x))
≔ @pathout_obj Z x x (@id Z x);

// Fixed-x source layer: evaluation at the reflexive outgoing path.
//
// Surface/formula:
//   pathout_refl_eval_func(Z,x)[E] = E[(x,id_x)].
//
// The base-arrow helper below records the concrete map along p; the full
// coherence package remains abstract.
symbol pathout_refl_eval_func [Z : Cat] (x : τ (Obj Z))
  : τ (Functor (@Catd_cat (@PathOut_cat Z x)) Cat_cat)
≔ @fapp0_func
     (@PathOut_cat Z x)
     Cat_cat
     (@pathout_refl_obj Z x);

// Internalized-x source layer: displayed package of fixed-source reflexive
// evaluation.
//
// Surface/formula:
//   PathOutReflEval_Z : x :^n Z ; Catd(PathOut_Z(x)) ⊢ Cat
//   PathOutReflEval_Z[x][E] = E[(x,id_x)].
constant symbol PathOutReflEval_funcd [Z : Cat]
  : τ (Functord (@PathOutMotives_catd Z) (@Const_catd Z Cat_cat));

rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $x
      (@PathOutReflEval_funcd $Z)
  ↪ @pathout_refl_eval_func $Z $x;

// Reflexive-to-path arrow in the outgoing-path category.
//
// Surface/formula:
//   rho_{x,y,p} : (x,id_x) ->^PathOut_Z(x) (y,p).
//
// This is the canonical Sigma transport arrow for Rep_Z(x). Its endpoint
// reduces by Rep_Z(x)[p](id_x) = p.
symbol pathout_refl_arrow [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y))
  : τ (Hom
      (@PathOut_cat Z x)
      (@pathout_refl_obj Z x)
      (@pathout_obj Z x y p))
≔ @sigma_transport_arrow
    Z
    (@Rep_catd Z x)
    x
    y
    p
    (@id Z x);

// Fixed-x source layer: motive transport along `rho_{x,y,p}`.
//
// Surface/formula:
//   E[rho_{x,y,p}] : E[(x,id_x)] ⊢ E[(y,p)].
symbol pathout_refl_eval_base_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat E (@pathout_refl_obj Z x))
      (Fibre_cat E (@pathout_obj Z x y p)))
≔ @fapp1_fapp0
    (@PathOut_cat Z x)
    Cat_cat
    E
    (@pathout_refl_obj Z x)
    (@pathout_obj Z x y p)
    (@pathout_refl_arrow Z x y p);

// Internalized-x source/target base layer: transport a motive along a moving
// source arrow.
//
// Surface/formula:
//   p_*E = PathOutMotives_Z[p](E)
//        = Pullback_catd(E, PathOut_transport_func(p))
//   so p_*E : PathOut_Z(y) ⊢ Cat.
symbol pathout_motive_transport_obj [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Catd (@PathOut_cat Z y))
≔ @fapp0
    (@Catd_cat (@PathOut_cat Z x))
    (@Catd_cat (@PathOut_cat Z y))
    (@fapp1_fapp0
      Z
      Cat_cat
      (@PathOutMotives_catd Z)
      x
      y
      p)
    E;

// Internalized-x source/target base layer: canonical total arrow in
// Σ x :^n Z, Catd(PathOut_Z(x)).
//
// Surface/formula:
//   (x,E) ->^Σ (y,p_*E), lying over p : x ->^Z y.
symbol pathout_motive_transport_arrow [Z : Cat]
  [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Hom
      (@Sigma_cat Z (@PathOutMotives_catd Z))
      (Struct_sigma x E)
      (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
≔ @sigma_transport_arrow
    Z
    (@PathOutMotives_catd Z)
    x
    y
    p
    E;

// Final desired fixed-x theorem/object: path induction section.
//
// Surface/formula:
//   path_ind_sec(x,E,u) : Π q :^n PathOut_Z(x), E[q]
//   with u : E[(x,id_x)].
symbol path_ind_sec [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x))))
  : τ (Obj (Pi_cat E));

// Fixed-x packaging layer: section collecting all `rho_{x,y,p}`, derived as
// path induction on the representable motive at the reflexive outgoing path.
//
// Surface/formula:
//   pathout_refl_arrow_sec(x) :
//     Π q :^n PathOut_Z(x), Hom_{PathOut_Z(x)}((x,id_x),q)
//   pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
symbol pathout_refl_arrow_sec [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (Pi_cat
      (@Rep_catd
        (@PathOut_cat Z x)
        (@pathout_refl_obj Z x))))
≔ @path_ind_sec
    Z
    x
    (@Rep_catd
      (@PathOut_cat Z x)
      (@pathout_refl_obj Z x))
    (@id (@PathOut_cat Z x) (@pathout_refl_obj Z x));

// Fixed-x internal layer: source family of path induction at fixed x.
//
// Surface/formula:
//   PathInd_src(Z,x)[E] = E[(x,id_x)].
symbol PathInd_src_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@Catd_cat (@PathOut_cat Z x)))
≔ @pathout_refl_eval_func Z x;

// Fixed-x internal layer: target family of path induction at fixed x.
//
// Surface/formula:
//   PathInd_tgt(Z,x)[E] = Π q :^n PathOut_Z(x), E[q].
symbol PathInd_tgt_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@Catd_cat (@PathOut_cat Z x)))
≔ @Pi_func (@PathOut_cat Z x);

// Fixed-x internal layer: component functor of the fixed-source eliminator.
//
// Surface/formula:
//   path_ind_func_fapp0(Z,x,E) : E[(x,id_x)] ⊢ Π q, E[q]
//   path_ind_func_fapp0(Z,x,E)[u] = path_ind_sec(Z,x,E,u).
symbol path_ind_func_fapp0 [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat E (@pathout_refl_obj Z x))
      (Pi_cat E));

rule @fapp0 _ _ (@path_ind_func_fapp0 $Z $x $E) $u
  ↪ @path_ind_sec $Z $x $E $u;

// Final desired fixed-x theorem packaged as a displayed functor.
//
// Surface/formula:
//   PathInd_func(Z,x) :
//     E :^n Catd(PathOut_Z(x)) ; E[(x,id_x)] ⊢ Π q, E[q].
constant symbol PathInd_func [Z : Cat] (x : τ (Obj Z))
  : τ (Functord
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x));

rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $E
      (@PathInd_func $Z $x)
  ↪ @path_ind_func_fapp0 $Z $x $E;

// Primary synthetic/telescope path-induction theorem over the varying source
// object.
//
// Surface/formula:
//   PathInd_transfd(Z) :
//     x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x]
//   PathInd_transfd(Z)[x] = PathInd_func(Z,x).
//
// Status/architecture note:
//   This `Transfd` is the primary internalized-x theorem. Its type already
//   internalizes naturality in the source object x; we should not re-express
//   that naturality as an external hand-written square for the core milestone.
//   What downstream regressions inspect are the induced source/target
//   transports along p : x ->^Z y:
//
//     source: E[rho_{x,y,p}]
//     target: section_pullback(PathOut_transport(p),E)
//
//   The target transport computes through the component-level displayed laxity
//   cell for `PathOutPi_funcd`; this is shared by the telescope theorem and its
//   derived Sigma-total presentation.
//
// The component projection rule is installed later, after the generic
// displayed-transfor head `tdapp0_fapp0` is declared.
constant symbol PathInd_transfd [Z : Cat]
  : τ (@Transfd
      Z
      (@PathOutMotives_catd Z)
      (@Const_catd Z Cat_cat)
      (@PathOutReflEval_funcd Z)
      (@PathOutPi_funcd Z));

// Internalized-x source layer: total source family over moving `(x,E)`.
//
// Surface/formula:
//   PathIndSrc_Z[(x,E)] = E[(x,id_x)]
//   over Σ x :^n Z, Catd(PathOut_Z(x)).
symbol PathIndSrc_catd [Z : Cat]
  : τ (Catd (@Sigma_cat Z (@PathOutMotives_catd Z)))
≔ @Sigma_catd_functord_catd
    Z
    (@PathOutMotives_catd Z)
    (@PathOutReflEval_funcd Z);

// Internalized-x source layer: source transport along the canonical total
// transported-motive arrow.
//
// Surface/formula:
//   PathIndSrc_transport(p,E) = E[rho_{x,y,p}]
//   : E[(x,id_x)] ⊢ (p_*E)[(y,id_y)] = E[(y,p)].
symbol PathIndSrc_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat (@PathIndSrc_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndSrc_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))))
≔ @pathout_refl_eval_base_func Z x y p E;

// Uncurried Sigma-total presentation of path induction, derived from the
// primary telescope theorem by generic Sigma-total uncurrying.
//
// Surface/formula:
//   PathInd_funcd(Z) :
//     x,E :^n Σ x :^n Z, Catd(PathOut_Z(x)) ;
//       E[(x,id_x)] ⊢ Π q :^n PathOut_Z(x), E[q]
//   PathInd_funcd(Z)[(x,E)][u] = path_ind_sec(Z,x,E,u).
//
// This is a derived presentation, not the primitive theorem. It is used to
// inspect the Sigma-style formulation at canonical/cartesian total arrows
// coming from transport of `(x,E)`. Arbitrary non-cartesian Sigma-arrow
// naturality is intentionally outside the current milestone.
symbol PathInd_funcd [Z : Cat]
  : τ (Functord
      (@PathIndSrc_catd Z)
      (@PathIndTgt_catd Z))
≔ @Sigma_transfd_funcd
    Z
    (@PathOutMotives_catd Z)
    (@PathOutReflEval_funcd Z)
    (@PathOutPi_funcd Z)
    (@PathInd_transfd Z);

/*
  Mathematical computation statements for fixed-x path induction.

  These describe the source/target fibres and the component of the packaged
  fixed-source eliminator. The Sigma-total component statements live with the
  generic uncurrying projection, after `tdapp0_fapp0` is available.
*/

// Transitivity benchmark layer: target family for composition out of a fixed
// source x.
//
// Surface/formula:
//   CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x)
//                      = Functord_cat(Rep_Z(y),Rep_Z(x)).
//
// This is a semantic `hom_con` alias, not a primitive stable family head. The
// transitivity benchmark checks that path induction on the corresponding
// motive computes to post/precomposition in representables.
injective symbol CompTarget_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd Z)
≔ @hom_con
    (@Catd_cat Z)
    (@Rep_catd Z x)
    (Op_cat Z)
    (@Rep_catd_func Z);

// Transitivity benchmark layer: readable alias for the capped hom-action of
// `CompTarget_catd`.
//
// Surface/formula:
//   CompTarget_Z(x)[p : a ->^Z b]
//     : (Rep_Z(a) ⊢ Rep_Z(x)) ⊢ (Rep_Z(b) ⊢ Rep_Z(x)).
//
// Its endpoint type uses canonical `Functord_cat` forms rather than reducible
// `Fibre_cat` wrappers, but its body still goes through `CompTarget_catd`
// itself.
symbol CompTarget_fapp1_func [Z : Cat] [x a b : τ (Obj Z)]
  (p : τ (Hom Z a b))
  : τ (Functor
      (@Functord_cat Z (@Rep_catd Z a) (@Rep_catd Z x))
      (@Functord_cat Z (@Rep_catd Z b) (@Rep_catd Z x)))
≔ @fapp1_fapp0
    Z
    Cat_cat
    (@CompTarget_catd Z x)
    a
    b
    p;

// Transitivity benchmark layer: composition motive over PathOut_Z(x).
//
// Surface/formula:
//   CompMotive_Z(x)[(y,p)] = Rep_Z(y) ⊢ Rep_Z(x).
//
// This is the pullback of `CompTarget_Z(x)` along the Sigma projection
// PathOut_Z(x) ⊢ Z.
symbol CompMotive_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@PathOut_cat Z x))
≔ @Sigma_proj1_pullback_catd
     Z
     (@Rep_catd Z x)
     (@CompTarget_catd Z x);

// Internalized classifier: pointwise opposite representable.
//
// Surface/formula:
//   Edge_Z(x)[y] = Hom_Z(x,y)^op.
symbol Edge_catd_func [Z : Cat]
  : τ (Functor (Op_cat Z) (Catd_cat Z))
≔ comp_cat_fapp0
     (@Op_catd_func Z)
     (@hom_int Z Z (@id_func Z));

// Internalized classifier: presheaf category over each fibre of a family.
//
// Surface/formula:
//   Presheaf_catd(K)[A][k] = A[k] ⊢ Cat.
symbol Presheaf_catd_func (K : Cat)
  : τ (Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Catd_cat K))
≔ comp_cat_fapp0
     (@fapp0_func (Catd_cat K) (Catd_cat K) (@Const_catd K Cat_cat))
     (@Functor_catd_func K);

// Internalized classifier: hom-presheaf family for a represented object.
//
// Surface/formula:
//   HomPresheaf_Z(x)[y] = Hom_Z(x,y)^op ⊢ Cat.
symbol HomPresheaf_catd_func [Z : Cat]
  : τ (Functor Z (Catd_cat (Op_cat Z)))
≔ comp_cat_fapp0
     (@Presheaf_catd_func (Op_cat Z))
     (@Op_func (Op_cat Z) (Catd_cat Z) (@Edge_catd_func Z));

// -------------------------------------------------------------------------------------------------
// 10. Directed homd target and internal homd functor
// -------------------------------------------------------------------------------------------------

/*
  Homd target architecture note:

  Mathematical notation:

    Edge_Z(x)(y)              = Hom_Z(x,y)^op
    HomPsh_Z(x)(y)            = Functor_cat(Hom_Z(x,y)^op, Cat)
    HomdTargetSection_E(x)(y) = E[y^-] ⊢_[y] HomPsh_Z(x)[y]
    HomdTarget_E[x]           = Π y :^n Z^op, HomdTargetSection_E(x)[y]

  `Homd_target_section_catd` and `Homd_target_catd` name these target-family
  expressions for readability and assertions. They are not used as required
  discriminants in the projection-rule LHSs below, because those positions are
  inferred implicit arguments and may reduce to canonical compound terms before
  matching.
*/

symbol Homd_target_section_catd [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  : τ (Catd (Op_cat Z))
≔ @Functor_catd
     (Op_cat Z)
     E
     (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x);

// Full target family of the internal displayed hom constructor.
//
// Surface/formula:
//   HomdTarget_E[x] =
//     Π y :^n Z^op, E[y^-] ⊢_[y] HomPsh_Z(x)[y].
symbol Homd_target_catd [Z : Cat] (E : τ (Catd Z))
  : τ (Catd Z)
≔ comp_cat_fapp0
     (comp_cat_fapp0
       (@Pi_func (Op_cat Z))
       (fapp0 (@Functor_catd_func (Op_cat Z)) E))
     (@HomPresheaf_catd_func Z);

// `homd_int` is a syntactic constructor package: its family arguments and
// displayed functor are recoverable from the head. Terminal-source behavior is
// still exposed through the stable projection rules below; avoid adding broad
// whole-family `homd_int` rewrites unless a later design explicitly needs them.
injective symbol homd_int : Π [Z : Cat], Π [D E : τ (Catd Z)],
  Π (FF : τ (Functord D E)),
  τ (Functord (Op_catd E) (@Homd_target_catd Z D));

// -------------------------------------------------------------------------------------------------
// 11. Endpoint normal forms for Sigma homs
// -------------------------------------------------------------------------------------------------

/*
  Covariant fibre-transport architecture:

    FibCovTarget_E[x]            = Transf_cat(hom_Z(x,-), E)
                                  ≡ Functord_cat(hom_Z(x,-), E)
    fib_cov_int(E)               : E ⊢ FibCovTarget_E
    fib_cov_src_func(E,x)        : E[x] ⊢ FibCovTarget_E[x]
    fib_cov_transf(E,x,u)        : hom_Z(x,-) => E
                                  ≡ Functord(hom_Z(x,-), E)
    fib_cov_tapp0_func(E,x,u,y)  : Hom_Z(x,y) ⊢ E[y]
    fib_cov_tapp0_func(E,x,u,y)(f) = E(f)(u)

  In the formal v3.2 normal form, a
  Cat-valued transfor is a displayed functor: `Transf_cat K Cat_cat F E`
  reduces to `Functord_cat K F E`. The declarations below keep the conceptual
  `FibCov_target_catd` family visible; assertions document the reduced heads.

  `fib_cov_tapp0_func` remains the functor-level normal form. The object-level
  action is just `fapp0 (fib_cov_tapp0_func E x y u) f`, so it is not named by
  a separate `fib_cov_tapp0_fapp0` alias in v3.2.
*/

// Internalized target family for covariant fibre transport.
//
// Surface/formula:
//   FibCov_target(E)[x] = Functord_cat(Rep_K(x),E).
symbol FibCov_target_catd [K : Cat] (E : τ (Catd K)) : τ (Catd K)
≔ @hom_con
    (@Catd_cat K)
    E
    (Op_cat K)
    (@hom_int K K (@id_func K));

// Internalized covariant fibre transport package.
//
// Surface/formula:
//   fib_cov_int(E)[x](u) : Rep_K(x) ⊢ E
//   fib_cov_int(E)[x](u)[y][f] = E[f](u).
constant symbol fib_cov_int : Π [K : Cat], Π (E : τ (Catd K)),
  τ (Functord E (@FibCov_target_catd K E));

// Component functor of `fib_cov_int` at x.
symbol fib_cov_src_func [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  : τ (Functor
      (Fibre_cat E x)
      (Fibre_cat (@FibCov_target_catd K E) x));

// Object component of `fib_cov_src_func`.
injective symbol fib_cov_transf [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Fibre_cat (@FibCov_target_catd K E) x));

rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $x
      (@fib_cov_int $K $E)
  ↪ @fib_cov_src_func $K $E $x;

rule fapp0 (@fib_cov_src_func $K $E $x) $u
  ↪ @fib_cov_transf $K $E $x $u;

rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $y
      (@fib_cov_transf $K $E $x $u)
  ↪ @fib_cov_tapp0_func $K $E $x $y $u;

rule @tapp0_fapp0
      (@Sigma_cat $Z (@hom_ $Z $Z (@id_func $Z) $x))
      Cat_cat
      (@Const_catd (@Sigma_cat $Z (@hom_ $Z $Z (@id_func $Z) $x)) Terminal_cat)
      $E
      (Struct_sigma $y $p)
      (@path_ind_sec $Z $x $E $u)
  ↪ @Obj_func
      (Fibre_cat $E (Struct_sigma $y $p))
      (@fapp0
        (Hom_cat (@PathOut_cat $Z $x)
          (@pathout_refl_obj $Z $x)
          (Struct_sigma $y $p))
        (Fibre_cat $E (Struct_sigma $y $p))
        (@fib_cov_tapp0_func
          (@PathOut_cat $Z $x)
          $E
          (@pathout_refl_obj $Z $x)
          (Struct_sigma $y $p)
          $u)
        (@pathout_refl_arrow $Z $x $y $p));

rule @path_ind_sec $Z $x
      (@Sigma_proj1_pullback_catd $Z (@hom_ $Z $Z (@id_func $Z) $x) $D)
      $u
  ↪ @fib_cov_transf $Z $D $x $u;

// Mathematical computation statement: fixed-x path induction on a
// Sigma-projection pullback motive reduces to covariant fibre transport.

// Final desired transitivity benchmark theorem/object.
//
// Surface/formula:
//   path_comp_sec(x) :
//     p :^n Rep_Z(x)[y] ; Rep_Z(y) ⊢ Rep_Z(x)
//   path_comp_sec(x)[p][z][q] = q ∘ p.
//
// This is the reduced normal form of fixed-x path induction on the composition
// motive.
symbol path_comp_sec [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (@Functord_cat Z (@Rep_catd Z x) (@CompTarget_catd Z x)))
≔ @fib_cov_transf
    Z
    (@CompTarget_catd Z x)
    x
    (@id_funcd Z (@Rep_catd Z x));

// Transitivity benchmark layer: representable action of a path by
// precomposition.
//
// Surface/formula:
//   path_comp_func(p) : Rep_Z(y) ⊢ Rep_Z(x)
//   path_comp_func(p)[z][q] = q ∘ p.
symbol path_comp_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functord (@Rep_catd Z y) (@Rep_catd Z x))
≔ @fapp1_fapp0
    (Op_cat Z)
    (@Catd_cat Z)
    (@Rep_catd_func Z)
    y
    x
    p;

/*
  Mathematical computation statements for the fixed-x transitivity benchmark.

  These are not merely regression probes: they state that fixed-x path
  induction on the composition motive computes to representable
  precomposition, and then to ordinary categorical composition.
*/

// The semantic `hom_con` presentation of `CompTarget_catd` computes without a
// CompTarget-specific identity shortcut.

/*
  Internal dependent-hom projection cascade:

    homd_int(FF) at x               ↪ homd_src_func(FF,x)
    homd_src_func(FF,x) at u        ↪ homd_src_sec(FF,x,u)
    homd_src_sec(FF,x,u) at y       ↪ homd_tgt_func(FF,x,u,y)
    homd_tgt_func(FF,x,u,y) at v    ↪ homd_(FF,x,u,y,v)

  The identity-specialized compatibility heads from v3.1/v3.2 migration have
  been retired; identity cases are written with `FF := id_funcd E`.
*/

// General first projection of `homd_int`: externalize x and the source fibre
// object in E, while the probe family D remains internal.
//
// Surface/formula:
//   homd_src_func(FF,x) : E[x]^op ⊢ Π y :^n Z^op, ...
symbol homd_src_func [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  : τ (Functor
        (Fibre_cat (@Op_catd Z E) x)
        (Pi_cat (@Homd_target_section_catd Z D x)));

// First projection fold. The source and target family arguments are
// deliberately `_`: their canonical forms contain reducible expressions such
// as `fapp0 (Op_catd_func Z) E` and `Homd_target_catd E`.  The Transf_cat
// unification helper above supplies the needed endpoint information.
rule @tapp0_fapp0
      $Z
      Cat_cat
      _
      _
      $x
      (@homd_int $Z $D $E $FF)
  ↪ @homd_src_func $Z $D $E $FF $x;

// General source-fixed projection after evaluating the component functor at u.
//
// Surface/formula:
//   homd_src_sec(FF,x,u)[y] = homd_tgt_func(FF,x,u,y).
symbol homd_src_sec [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (@Homd_target_section_catd Z D x)));

// Second projection fold: externalize x,u and keep the y,v endpoint internal.
rule fapp0 (@homd_src_func $Z $D $E $FF $x) $u
  ↪ @homd_src_sec $Z $D $E $FF $x $u;

// If the target family of FF is terminal, the first projection is a constant
// functor out of the terminal source fibre. This generalizes the old
// identity-specialized terminal-source normal form.
rule @homd_src_func $Z $D (@Const_catd $Z Terminal_cat) $FF $x
  ↪ @Obj_func
      (Pi_cat (@Homd_target_section_catd $Z $D $x))
      (@homd_src_sec $Z $D (@Const_catd $Z Terminal_cat) $FF $x Terminal_obj);

// General inner endpoint functor after projecting the source-fixed section at y.
//
// Surface/formula:
//   homd_tgt_func(FF,x,u,y)[v] = homd_(FF,x,u,y,v).
symbol homd_tgt_func [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  : τ (Functor
        (Fibre_cat D y)
        (Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat));

// Terminal-source normal form for the generalized inner endpoint. This exposes
// the same homd-valued family used by piapp1_func without adding a broad
// whole-family homd_int rewrite.
rule @homd_tgt_func $Z (@Const_catd $Z Terminal_cat) $E $s $x $u $y
  ↪ Obj_func
      (homd_ 
        (@id_funcd $Z $E)
        $x $u
        $y (@piapp0 $Z $E $s $y));

// Third projection fold. In v3.2 `piapp0` is a definition through ordinary
// terminal-source component evaluation, so this rule lives one layer down at
// the `tapp0_fapp0` component. The inferred source/target family arguments are
// deliberately `_` for the same stable-head hygiene as the other homd folds.
rule @tapp0_fapp0
      (Op_cat $Z)
      Cat_cat
      (@Const_catd (Op_cat $Z) Terminal_cat)
      _
      $y
      (@homd_src_sec $Z $D $E $FF $x $u)
  ↪ @Obj_func
      (Fibre_cat (@Homd_target_section_catd $Z $D $x) $y)
      (@homd_tgt_func $Z $D $E $FF $x $u $y);

// Constant-family section evaluation follows ordinary functor application.
rule @tapp0_fapp0
      $K
      Cat_cat
      (@Const_catd $K Terminal_cat)
      (@Const_catd $K $A)
      $k
      $F
  ↪ @Obj_func $A (@fapp0 $K $A $F $k);

// Final endpoint fold. At this point the stable head `homd_` carries the
// endpoint family; pointwise object-action is handled by unfolding `homd_`.
rule fapp0 (@homd_tgt_func $Z $D $E $FF $x $u $y) $v
  ↪ @homd_ $Z $D $E $FF $x $u $y $v;

// -------------------------------------------------------------------------------------------------
// 12. Section action over dependent homs
// -------------------------------------------------------------------------------------------------

/*
  Section action source endpoint.

  Mathematical notation:
    s[x]                = piapp0 s x
    piapp1_src_obj(s,f) = E(f)(s[x]).

  The full `piapp1_func`/`piapp1_fapp0` package is defined after the displayed
  internal-hom projection heads it unfolds through.
*/
symbol piapp1_src_obj [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Obj (Fibre_cat E y))
≔ fapp0 (@fib_cov_tapp0_func K E x y (@piapp0 K E s x)) f;

// -------------------------------------------------------------------------------------------------
// 13. Internal displayed hom-action heads
// -------------------------------------------------------------------------------------------------

/*
  Mathematical notation:
    tdapp1_int_func_transfd(FF,GG)
      : Transfd(FF,GG) ⊢ Transfd(homd_int(id_E), homd_int(GG) ∘ FF^op)

    tdapp1_int_fapp0_transfd(ϵ)
      = the internal displayed hom-action of ϵ

    fdapp1_int_transfd(FF)
      = tdapp1_int_fapp0_transfd(id_FF)

  Current laxity architecture:

    internal hom-action, then extracted laxity, then Sigma action consumes laxity.

  The Sigma-total presentation is the externalization/test surface where a
  laxity cell is visible as a fibre component of a total arrow. It is not the
  primitive source of that same laxity; otherwise `Sigma(FF)` would be defined
  using `laxity(FF,p)` and `laxity(FF,p)` would be extracted back from
  `Sigma(FF)`, which is circular.

  The intended non-circular source for displayed functor laxity is the
  identity-specialized internal displayed hom-action:

    fdapp1_int_transfd(FF)
      : Transfd(homd_int(id_E), homd_int(FF) o Op_funcd(FF)).

  Applying this to a canonical/cartesian dependent-hom triangle should expose
  the component

    D[p](FF[x](u)) ->^(D[y]) FF[y](E[p](u)).

  The active implementation stops at this component-level normal form,
  `fdapp1_int_cell(FF,p,u)`. A future whole-transfor interface
  should be added only after the source object `u` can be internalized without
  obscuring this extraction path. Strict constructors then need explicit folds
  making their laxity collapse to the identity/cartesian component.
*/
symbol tdapp1_int_func_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  τ (Functor
      (Transfd_cat FF GG)
      (Transfd_cat
        (homd_int (@id_funcd K E))
        (comp_catd_fapp0
          (homd_int GG)
          (Op_funcd FF))));

// Object action of `tdapp1_int_func_transfd`.
symbol tdapp1_int_fapp0_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  Π (ϵ : τ (Transfd FF GG)),
  τ (Transfd
      (homd_int (@id_funcd K E))
      (comp_catd_fapp0
        (homd_int GG)
        (Op_funcd FF)));

rule fapp0 (@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ
  ↪ @tdapp1_int_fapp0_transfd $K $E $D $FF $GG $ϵ;

// Hom action of `tdapp1_int_func_transfd`.
symbol tdapp1_int_fapp1_func_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  Π (ϵ ϵ' : τ (Transfd FF GG)),
  τ (Functor
      (Hom_cat (Transfd_cat FF GG) ϵ ϵ')
      (Hom_cat
        (Transfd_cat
          (homd_int (@id_funcd K E))
          (comp_catd_fapp0
            (homd_int GG)
            (Op_funcd FF)))
        (tdapp1_int_fapp0_transfd ϵ)
        (tdapp1_int_fapp0_transfd ϵ')));

rule @fapp1_func _ _ (@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ $ϵ'
  ↪ @tdapp1_int_fapp1_func_transfd $K $E $D $FF $GG $ϵ $ϵ';

// Identity-specialized displayed internal hom-action.
symbol fdapp1_int_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π (FF : τ (Functord E D)),
  τ (Transfd
      (homd_int (@id_funcd K E))
      (comp_catd_fapp0
        (homd_int FF)
        (Op_funcd FF)));

// Identity-specialization fold for the internal displayed hom-action.
rule @tdapp1_int_fapp0_transfd $K $E $D $FF $FF
      (@id_transfd $K $E $D $FF)
  ↪ @fdapp1_int_transfd $K $E $D $FF;

// -------------------------------------------------------------------------------------------------
// 14. Derived displayed component notation
// -------------------------------------------------------------------------------------------------

/*
  Fibre-level notation for displayed functors and displayed transfors.

  Mathematical notation:

    Fibre_func(FF,z)          = FF[z] : E[z] ⊢ D[z]
    tdapp0_func(z)            : Transfd(FF,GG) ⊢ Transf(FF[z],GG[z])
    tdapp0_fapp0(z,ϵ)         = ϵ_z : FF[z] => GG[z]
    Fibre_transf(ϵ,z)         = ϵ_z
    Fibre_transf_app(ϵ,z,u)   = ϵ_z(u)

  `tdapp0_func` and `tdapp0_fapp0` are stable projection heads: later rewrite
  rules attach to them directly. The `Fibre_*` names are readable definitions
  over these heads, not additional kernel rewrite surfaces.
*/
// Fibre functor of a displayed functor at z.
symbol Fibre_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (z : τ (Obj K))
  : τ (Functor (Fibre_cat E z) (Fibre_cat D z))
≔ @tapp0_fapp0 K Cat_cat E D z FF;

// Component projection functor for displayed transfors at z.
symbol tdapp0_func [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (z : τ (Obj K))
  : τ (Functor
      (Transfd_cat FF GG)
      (Transf_cat (Fibre_func FF z) (Fibre_func GG z)));

// Capped displayed-transfor component.
symbol tdapp0_fapp0 [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (z : τ (Obj K))
  (ϵ : τ (Transfd FF GG))
  : τ (Transf (Fibre_func FF z) (Fibre_func GG z));

rule fapp0 (@tdapp0_func $K $E $D $FF $GG $z) $ϵ
  ↪ @tdapp0_fapp0 $K $E $D $FF $GG $z $ϵ;

// Component projection for the primary synthetic/telescope path-induction
// theorem. This lives here because `tdapp0_fapp0` is the generic displayed
// transfor component head.
rule @tdapp0_fapp0
      $Z
      _
      _
      _
      _
      $x
      (@PathInd_transfd $Z)
  ↪ @PathInd_func $Z $x;

// Object-component projection for generic Sigma-total uncurrying.
rule @tapp0_fapp0
      (@Sigma_cat $K $R)
      Cat_cat
      _
      _
      (Struct_sigma $k $r)
      (@Sigma_transfd_funcd $K $R $S $T $eta)
  ↪ @tapp0_fapp0
      (Fibre_cat $R $k)
      Cat_cat
      (@Fibre_func $K $R (@Const_catd $K Cat_cat) $S $k)
      (@Fibre_func $K $R (@Const_catd $K Cat_cat) $T $k)
      $r
      (@tdapp0_fapp0
        $K
        $R
        (@Const_catd $K Cat_cat)
        $S
        $T
        $k
        $eta);

/*
  Mathematical computation statements for synthetic/telescope path induction.

  Surface/formula:
    PathInd_transfd(Z)[x]       = PathInd_func(Z,x)
    PathInd_transfd(Z)[x][E]    = path_ind_func_fapp0(Z,x,E)
    PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u).
*/

// First transitivity benchmark rerouted through the synthetic/telescope
// theorem component.

// Fully expanded transitivity benchmark through the synthetic/telescope
// theorem component.

/*
  Generic Sigma-total uncurrying and the path-induction specialization.

  Surface/formula:
    Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r]
    PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E).
*/

// Sigma-total presentation of the transitivity benchmark, using the derived
// `PathInd_funcd` component rather than the telescope component directly.

// Fully expanded transitivity benchmark through the Sigma-total presentation.

// Readable component alias.
symbol Fibre_transf [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (z : τ (Obj K))
  : τ (Transf (Fibre_func FF z) (Fibre_func GG z))
≔ @tdapp0_fapp0 K E D FF GG z ϵ;

// Object action of a displayed-transfor component.
symbol Fibre_transf_app [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (z : τ (Obj K))
  (u : τ (Obj (Fibre_cat E z)))
  : τ (Hom
      (Fibre_cat D z)
      (fapp0 (Fibre_func FF z) u)
      (fapp0 (Fibre_func GG z) u))
≔ @tapp0_fapp0
     (Fibre_cat E z)
     (Fibre_cat D z)
     (@Fibre_func K E D FF z)
     (@Fibre_func K E D GG z)
     u
     (@Fibre_transf K E D FF GG ϵ z);

// Fixed-base layer: component of an arrow between sections.
//
// Mathematical notation:
//   pi_hom_fapp0(eta,k) = eta[k] : s[k] ->^(E[k]) t[k]
//   for eta : Hom_{Π i :^n K, E[i]}(s,t).
//
// Faithful surface syntax:
//   eta[k] : s[k] ->^(E[k]) t[k].
//
// This is a semantic definition over the existing displayed component
// projection. There is intentionally no rewrite rule targeting `piapp0_func`:
// that head is definable, so it is not a rewrite discriminator.
symbol pi_hom_fapp0 [K : Cat] [E : τ (Catd K)]
  [s t : τ (Obj (Pi_cat E))]
  (eta : τ (Hom (Pi_cat E) s t))
  (k : τ (Obj K))
  : τ (Hom (Fibre_cat E k) (piapp0 s k) (piapp0 t k))
≔ tapp0_fapp0 Terminal_obj (tdapp0_fapp0 k eta);

// Internalized-x prerequisite: heterogeneous action of a displayed functor over
// a base arrow. This is the Cat-valued specialization of the ordinary transfor
// hom-action.
//
// Surface/formula:
//   FF[p] : E[x] ⊢ D[y]
//   for FF : k :^n K ; E[k] ⊢ D[k] and p : x ->^K y.
symbol functord_transport_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y))
≔ @tapp1_fapp0 K Cat_cat E D x y FF p;

// Internalized-x coherence route: first apply FF at x, then transport in D.
//
// Surface/formula:
//   D[p] ∘ FF[x] : E[x] ⊢ D[y].
symbol functord_transport_lhs_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y))
≔ @comp_cat_fapp0
    (Fibre_cat E x)
    (Fibre_cat D x)
    (Fibre_cat D y)
    (@catd_transport_func K D x y p)
    (@Fibre_func K E D FF x);

// Internalized-x coherence route: first transport in E, then apply FF at y.
//
// Surface/formula:
//   FF[y] ∘ E[p] : E[x] ⊢ D[y].
symbol functord_transport_rhs_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y))
≔ @comp_cat_fapp0
    (Fibre_cat E x)
    (Fibre_cat E y)
    (Fibre_cat D y)
    (@Fibre_func K E D FF y)
    (@catd_transport_func K E x y p);

/*
  Deferred whole-transfor displayed laxity interface.

  Intended future surface:

    functord_laxity_transf(FF,p)
      : D[p] o FF[x] => FF[y] o E[p].

  Intended declaration, deliberately not active yet:

    symbol functord_laxity_transf [K : Cat] [E D : τ (Catd K)]
      (FF : τ (Functord E D))
      [x y : τ (Obj K)]
      (p : τ (Hom K x y))
      : τ (@Transf
          (Fibre_cat E x)
          (Fibre_cat D y)
          (@functord_transport_lhs_func K E D FF x y p)
          (@functord_transport_rhs_func K E D FF x y p));

  The active implementation stops at the component-level cell
  `fdapp1_int_cell(FF,p,u)`. Reintroduce the live symbol only after
  the `fdapp1_int_transfd` extraction internalizes `u` cleanly enough to support
  the whole `Transf` computationally.
*/

// Capped object action of the extracted displayed internal-hom functor.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,v][p][alpha]
//     : D[p](FF[x]u) ->^(D[y]) FF[y]v.
//
// Faithful surface syntax:
//   the Sigma-map fibre component induced by the internal displayed hom-action.
//
// This is deliberately the owner of the Sigma-map fibre component. The surface
// reading may be `FF[y][alpha] o laxity(FF,p)[u]`, but the kernel normal form is
// this direct projection from the internal-hom action, not a reconstructed
// composite through an artificial `FF[y][alpha]` head.
symbol fdapp1_int_hom_fapp0 [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  [v : τ (Obj (Fibre_cat E y))]
  (alpha : τ (Hom
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u)
      v))
  : τ (Hom
      (Fibre_cat D y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y p)
        u)
      (@fapp0
        (Fibre_cat E y)
        (Fibre_cat D y)
        (@Fibre_func K E D FF y)
        v));

// Arrow action of a Sigma map on the canonical Sigma-hom constructor.
//
// Surface/formula:
//   Sigma(FF)[(p,alpha)]
//     = (p, fdapp1_int(FF)[x,u][y,v][p][alpha]).
//
// This is the capped action `fapp1_fapp0` of `sigma_map_func`. The corresponding
// fixed-endpoint hom-action package is folded later, after
// `fdapp1_int_presheaf_arrow` is available.
rule @fapp1_fapp0
      _
      _
      (@sigma_map_func $K $E $D $η)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
      (Struct_sigma $p $alpha)
  ↪ @sigma_arrow
      $K
      $D
      $x
      $y
      (@fapp0
        (Fibre_cat $E $x)
        (Fibre_cat $D $x)
        (@tapp0_fapp0 $K Cat_cat $E $D $x $η)
        $u)
      (@fapp0
        (Fibre_cat $E $y)
        (Fibre_cat $D $y)
        (@tapp0_fapp0 $K Cat_cat $E $D $y $η)
        $v)
      $p
      (@fdapp1_int_hom_fapp0
        $K
        $E
        $D
        $η
        $x
        $y
        $p
        $u
        $v
        $alpha);

// Source dependent-hom section used by the internal-hom extraction.
//
// Mathematical notation:
//   homd_id_src_sec(E,x,u)
//     = homd_int(id_E)[x](u)
//     : Π y :^n K^op, E[y^-] ⊢_[y] (Hom_K(x,y)^op ⊢ Cat).
//
// Faithful surface syntax:
//   Homd_E(x,u,—,—).
symbol homd_id_src_sec [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (Homd_target_section_catd E x)))
≔ homd_src_sec (@id_funcd K E) x u;

// Target dependent-hom section obtained by applying FF to the source object.
//
// Mathematical notation:
//   homd_ff_src_sec(FF,x,u)
//     = homd_int(FF)[x](FF[x](u))
//     : Π y :^n K^op, E[y^-] ⊢_[y] (Hom_K(x,y)^op ⊢ Cat).
//
// Faithful surface syntax:
//   Homd_D(x,FF[x](u),—,FF[—](—)).
symbol homd_ff_src_sec [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (Homd_target_section_catd E x)))
≔ homd_src_sec FF x (fapp0 (Fibre_func FF x) u);

// First concrete stage of the non-circular laxity extraction path. This is the
// component of the internal displayed hom-action at the represented source x
// and source fibre object u. Its source is the identity dependent-hom section;
// its target is the section obtained by first applying FF at x and then using
// `homd_int(FF)`.
//
// Mathematical notation:
//   fdapp1_section(FF,x,u) :
//     homd_int(id_E)[x](u) ->^(HomdTarget_E[x]) homd_int(FF)[x](FF[x](u)).
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u] :
//     Homd_E(x,u,—,—) ->^(HomdTarget_E[x]) Homd_D(x,FF[x](u),—,FF[—](—)).
//
// Further projections at y, at the transported object E[p](u), and at the base
// arrow p produce the component-level displayed laxity cell.
symbol fdapp1_int_section_arrow [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat (Homd_target_catd E) x)
      (homd_id_src_sec E x u)
      (homd_ff_src_sec FF x u));

rule @tapp0_fapp0
      _
      _
      _
      _
      $u
      (@tdapp0_fapp0
        $K
        _
        _
        _
        _
        $x
        (@fdapp1_int_transfd $K $E $D $FF))
  ↪ @fdapp1_int_section_arrow $K $E $D $FF $x $u;

// Source y-component of the identity dependent-hom section.
//
// Mathematical notation:
//   homd_id_tgt_func(E,x,u,y)
//     = homd_int(id_E)[x](u)[y].
//
// Faithful surface syntax:
//   Homd_E(x,u,y,—).
symbol homd_id_tgt_func [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Functor
      (Fibre_cat E y)
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
≔ piapp0 (homd_id_src_sec E x u) y;

// Target y-component after applying FF to the source object.
//
// Mathematical notation:
//   homd_ff_tgt_func(FF,x,u,y)
//     = homd_int(FF)[x](FF[x](u))[y].
//
// Faithful surface syntax:
//   Homd_D(x,FF[x](u),y,FF[y](—)).
symbol homd_ff_tgt_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Functor
      (Fibre_cat E y)
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
≔ piapp0 (homd_ff_src_sec FF x u) y;

// Second projection stage of the same internal-hom extraction path.
//
// Mathematical notation:
//   fdapp1_section(FF,x,u)[y] :
//     homd_int(id_E)[x](u)[y]
//       => homd_int(FF)[x](FF[x](u))[y].
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y] :
//     Homd_E(x,u,y,—) => Homd_D(x,FF[x](u),y,FF[y](—)).
//
// The type is written in the reduced `Transf` form because the next projection
// consumes it through `tapp0_fapp0`. This still keeps the codomain functor in
// the canonical `Hom_K(x,y)^op ⊢ Cat` form, avoiding the reducible
// `Fibre_cat(HomPresheaf_Z(x),y)` classifier pipeline.
symbol fdapp1_int_tgt_arrow [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Transf
      (homd_id_tgt_func E x u y)
      (homd_ff_tgt_func FF x u y));

rule @tapp0_fapp0
      _
      _
      _
      _
      Terminal_obj
      (@tdapp0_fapp0
        _
        _
        _
        _
        _
        $y
        (@fdapp1_int_section_arrow $K $E $D $FF $x $u))
  ↪ @fdapp1_int_tgt_arrow $K $E $D $FF $x $u $y;

// Third projection stage: evaluate the y-component at a fibre object v.
//
// Mathematical notation:
//   fdapp1_section(FF,x,u)[y][v] :
//     homd_int(id_E)[x](u)[y](v)
//       ->^(HomPsh_Z(x)[y]) homd_int(FF)[x](FF[x](u))[y](v).
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y,v] :
//     Hom_E(E[—](u),v) => Hom_D(D[—](FF[x](u)),FF[y](v)).
//
// The ambient category is written directly as `Hom_K(x,y)^op ⊢ Cat`, rather
// than through `Fibre_cat(HomPresheaf_Z(x),y)`. This is the canonical endpoint
// category of the HomPresheaf classifier and avoids making later projections
// depend on unfolding the whole classifier pipeline.
symbol fdapp1_int_presheaf_arrow [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
      (fapp0 (homd_id_tgt_func E x u y) v)
      (fapp0 (homd_ff_tgt_func FF x u y) v));

rule @tapp0_fapp0
      _
      _
      _
      _
      $v
      (@fdapp1_int_tgt_arrow $K $E $D $FF $x $u $y)
  ↪ @fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v;

// Full hom-action of a Sigma map between fixed endpoints.
//
// The hom category of a Sigma total is stored as the opposite of a dependent
// Sigma over the opposite base hom. Therefore the functor-level action is the
// opposite of the Sigma map induced by the internal displayed-hom projection:
//   (p,alpha) |-> (p, fdapp1_int(FF)[x,u][y,v][p][alpha]).
rule @fapp1_func
      _
      _
      (@sigma_map_func $K $E $D $FF)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
  ↪ @Op_func
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (fapp0 (@homd_id_tgt_func $K $E $x $u $y) $v))
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (fapp0 (@homd_ff_tgt_func $K $E $D $FF $x $u $y) $v))
      (@sigma_map_func
        (Op_cat (Hom_cat $K $x $y))
        (fapp0 (@homd_id_tgt_func $K $E $x $u $y) $v)
        (fapp0 (@homd_ff_tgt_func $K $E $D $FF $x $u $y) $v)
        (@fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v));

// Fourth projection stage, with endpoints written directly through `homd_`.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,v][p] :
//     homd_(id_E,x,u,y,v)[p]
//       ⊢ homd_(FF,x,FF[x](u),y,v)[p].
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y,v][p].
//
// This deliberately keeps the endpoints at the stable `homd_` layer. A later
// fold/assertion can expose the simplified fibre-hom category
// `Hom_{D[y]}(D[p](FF[x](u)),FF[y](v))` when a theorem needs that shape.
symbol fdapp1_int_hom_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      Cat_cat
      (fapp0
        (homd_
          (@id_funcd K E)
          x
          u
          y
          v)
        p)
      (fapp0
        (homd_
          FF
          x
          (fapp0 (Fibre_func FF x) u)
          y
          v)
        p));

rule @fapp1_fapp0
      _
      Cat_cat
      (@fapp0_func _ _ $p)
      _
      _
      (@fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v)
  ↪ @fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v;

rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $p
      (@fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v)
  ↪ @fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v;

rule fapp0
      (@fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v)
      $alpha
  ↪ @fdapp1_int_hom_fapp0 $K $E $D $FF $x $y $p $u $v $alpha;

/*
  Full section action over a base arrow.

  Mathematical notation:
    s[f]                  = piapp1_fapp0 s f : E(f)(s[x]) ->^(E[y]) s[y]
    piapp1_func(s,x,y)[f] = s[f].

  The section action is the terminal-source specialization of the displayed
  internal hom action, projected to the presheaf arrow level.
*/
symbol piapp1_func [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  : τ (Obj (Pi_cat
      (homd_
        (@id_funcd K E)
        x (@piapp0 K E s x)
        y (@piapp0 K E s y))))
≔ @fdapp1_int_presheaf_arrow
    K
    (@Const_catd K Terminal_cat)
    E
    s
    x
    Terminal_obj
    y
    Terminal_obj;

// Capped section action over a base arrow.
//
// Surface/formula:
//   piapp1_fapp0(s,f) = s[f] : E[f](s[x]) ->^(E[y]) s[y].
symbol piapp1_fapp0 [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Hom
      (Fibre_cat E y)
      (@piapp1_src_obj K E s x y f)
      (@piapp0 K E s y))
≔ piapp0 (@piapp1_func K E s x y) f;

// Raw canonical-triangle cell extracted from the internal displayed hom-action.
// This is the stable component-level displayed laxity normal form.
// The concrete transported-object identity is consumed directly by the
// `fdapp1_int_hom_fapp0` rule below.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,E[p]u][p](id)
//     : D[p](FF[x](u)) ->^(D[y]) FF[y](E[p](u)).
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y,E[p]u][p](id).
symbol fdapp1_int_cell [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat D y)
      (fapp0 (functord_transport_lhs_func FF p) u)
      (fapp0 (functord_transport_rhs_func FF p) u));

rule @fdapp1_int_hom_fapp0
      $K
      $E
      $D
      $FF
      $x
      $y
      $p
      $u
      _
      (@id
        _
        _)
  ↪ @fdapp1_int_cell $K $E $D $FF $x $y $p $u;

rule @fdapp1_int_hom_fapp0
      $K
      (@Const_catd $K Terminal_cat)
      $D
      $FF
      $x
      $y
      $p
      Terminal_obj
      Terminal_obj
      Terminal_obj
  ↪ @fdapp1_int_cell
      $K
      (@Const_catd $K Terminal_cat)
      $D
      $FF
      $x
      $y
	      $p
	      Terminal_obj;

/*
  Generic displayed internal-hom action projections.

  These are the arbitrary displayed-transfor counterparts of the
  identity-specialized `fdapp1_int_*` extraction path.

  Mathematical notation:
    epsilon : FF => GG
    homd_tdapp1_src_sec(FF,GG,x,u)
      = homd_int(GG)[x](FF[x](u))

    tdapp1_int_section_arrow(epsilon,x,u)
      : homd_int(id_E)[x](u)
          ->^(HomdTarget_E[x]) homd_int(GG)[x](FF[x](u))

    tdapp1_int_cell(epsilon,p,u)
      : D[p](FF[x](u)) ->^(D[y]) GG[y](E[p](u)).

  Faithful surface syntax:
    epsilon[p][u] : D[p](FF[x] u) ->^(D[y]) GG[y](E[p] u)

  The rules below project this cell through the same stages as
  `fdapp1_int_*`: section at x,u; target y; fibre object v; base arrow p; then
  the identity fibre arrow. When epsilon is the displayed identity, these heads
  fold back to the corresponding `fdapp1_int_*` normal forms.
*/
symbol homd_tdapp1_src_sec [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (Homd_target_section_catd E x)))
≔ @homd_src_sec
    K
    E
    D
    GG
    x
    (fapp0 (@Fibre_func K E D FF x) u);

symbol homd_tdapp1_tgt_func [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Functor
      (Fibre_cat E y)
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
≔ piapp0 (@homd_tdapp1_src_sec K E D FF GG x u) y;

symbol tdapp1_int_section_arrow [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat (Homd_target_catd E) x)
      (homd_id_src_sec E x u)
      (@homd_tdapp1_src_sec K E D FF GG x u));

rule @tapp0_fapp0
      _
      _
      _
      _
      $u
      (@tdapp0_fapp0
        $K
        _
        _
        _
        _
        $x
        (@tdapp1_int_fapp0_transfd $K $E $D $FF $GG $ϵ))
  ↪ @tdapp1_int_section_arrow $K $E $D $FF $GG $ϵ $x $u;

rule @tdapp1_int_section_arrow
      $K
      $E
      $D
      $FF
      $FF
      (@id_transfd $K $E $D $FF)
      $x
      $u
  ↪ @fdapp1_int_section_arrow $K $E $D $FF $x $u;

symbol tdapp1_int_tgt_arrow [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Transf
      (homd_id_tgt_func E x u y)
      (@homd_tdapp1_tgt_func K E D FF GG x u y));

rule @tapp0_fapp0
      _
      _
      _
      _
      Terminal_obj
      (@tdapp0_fapp0
        _
        _
        _
        _
        _
        $y
        (@tdapp1_int_section_arrow $K $E $D $FF $GG $ϵ $x $u))
  ↪ @tdapp1_int_tgt_arrow $K $E $D $FF $GG $ϵ $x $u $y;

rule @tdapp1_int_tgt_arrow
      $K
      $E
      $D
      $FF
      $FF
      (@id_transfd $K $E $D $FF)
      $x
      $u
      $y
  ↪ @fdapp1_int_tgt_arrow $K $E $D $FF $x $u $y;

symbol tdapp1_int_presheaf_arrow [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
      (fapp0 (homd_id_tgt_func E x u y) v)
      (fapp0 (@homd_tdapp1_tgt_func K E D FF GG x u y) v));

rule @tapp0_fapp0
      _
      _
      _
      _
      $v
      (@tdapp1_int_tgt_arrow $K $E $D $FF $GG $ϵ $x $u $y)
  ↪ @tdapp1_int_presheaf_arrow $K $E $D $FF $GG $ϵ $x $u $y $v;

rule @tdapp1_int_presheaf_arrow
      $K
      $E
      $D
      $FF
      $FF
      (@id_transfd $K $E $D $FF)
      $x
      $u
      $y
      $v
  ↪ @fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v;

symbol tdapp1_int_hom_func [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      Cat_cat
      (fapp0
        (homd_
          (@id_funcd K E)
          x
          u
          y
          v)
        p)
      (fapp0
        (homd_
          GG
          x
          (fapp0 (Fibre_func FF x) u)
          y
          v)
        p));

rule @fapp1_fapp0
      _
      Cat_cat
      (@fapp0_func _ _ $p)
      _
      _
      (@tdapp1_int_presheaf_arrow $K $E $D $FF $GG $ϵ $x $u $y $v)
  ↪ @tdapp1_int_hom_func $K $E $D $FF $GG $ϵ $x $y $p $u $v;

rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $p
      (@tdapp1_int_presheaf_arrow $K $E $D $FF $GG $ϵ $x $u $y $v)
  ↪ @tdapp1_int_hom_func $K $E $D $FF $GG $ϵ $x $y $p $u $v;

rule @tdapp1_int_hom_func
      $K
      $E
      $D
      $FF
      $FF
      (@id_transfd $K $E $D $FF)
      $x
      $y
      $p
      $u
      $v
  ↪ @fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v;

symbol tdapp1_int_cell [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat D y)
      (fapp0 (functord_transport_lhs_func FF p) u)
      (fapp0 (functord_transport_rhs_func GG p) u));

rule fapp0
      (@tdapp1_int_hom_func $K $E $D $FF $GG $ϵ $x $y $p $u _)
      (@id
        _
        _)
  ↪ @tdapp1_int_cell $K $E $D $FF $GG $ϵ $x $y $p $u;

rule @tdapp1_int_cell
      $K
      $E
      $D
      $FF
      $FF
      (@id_transfd $K $E $D $FF)
      $x
      $y
      $p
      $u
  ↪ @fdapp1_int_cell $K $E $D $FF $x $y $p $u;

rule @fdapp1_int_cell
      $K
      (@Const_catd $K Terminal_cat)
      (@Const_catd $K $A)
      $s
      $x
      $y
      $p
      Terminal_obj
  ↪ @fapp1_fapp0 $K $A $s $x $y $p;

// Representable precomposition is strict/cartesian: its displayed laxity
// component is the identity at the composite arrow. The rule keys on the
// stable `Rep_transport_func` head and keeps the family slots implicit.
rule @fdapp1_int_cell
      $Z
      _
      _
      (@Rep_transport_func $Z $x $y $p)
      $y
      $z
      $q
      (@id $Z $y)
  ↪ @id
      (Hom_cat $Z $x $z)
      (@comp_fapp0 $Z $x $y $z $q $p);

// Representable precomposition is strict/cartesian already at the Sigma-map
// fibre projection: applying the internal-hom action to the canonical identity
// fibre arrow gives the identity at the composite arrow.
rule @fdapp1_int_hom_fapp0
      $Z
      _
      _
      (@Rep_transport_func $Z $x $y $p)
      $y
      $z
      $q
      (@id $Z $y)
      $q
      (@id (Hom_cat $Z $y $z) $q)
  ↪ @id
      (Hom_cat $Z $x $z)
      (@comp_fapp0 $Z $x $y $z $q $p);

// -------------------------------------------------------------------------------------------------
// 15. Generic Sigma/Pi weakening helpers
// -------------------------------------------------------------------------------------------------

/*
  Generic Sigma/Pi weakening/evaluation helpers.

    sigma_intro_transf(E)             : E ⊢ const(ΣE)
    sigma_intro_tapp0_func(E,k)       : E[k] ⊢ ΣE
    sigma_intro_tapp0_func(E,k)(u)    = (k,u)

    pi_eval_transf(E)                 : const(ΠE) ⊢ E
    pi_eval_transf(E)[k]              = piapp0_func(E,k) : ΠE ⊢ E[k]

    const_section_func(K,A)           : A ⊢ Π (k :^n K), A
    const_section_func(K,A)(a)        = const(a)

    section_pullback_func(F,E)        : Π_B E ⊢ Π_A F^*E
    section_pullback_func(F,E)(s)(a)  = s(Fa)

  The arrow action of `sigma_intro_tapp0_func` is intentionally deferred. It
  should eventually send a fibre arrow α : u ->^(E[k]) v to the corresponding
  total arrow (id_k, α), but the clean rule needs the identity/fibre-transport
  normal forms for Sigma homs.

  `section_pullback_func` remains the current surface helper. A future internal
  version should be `section_pullback_int`, indexed over the functor argument F,
  with the pullback-family functor built from `comp_cat_cov_func E` and then
  composed with `Pi_func`, in the same style as the remaining `homd_int` and
  displayed-action projection packages.
*/
// Generic Sigma helper: include a fibre object as a total object.
//
// Surface/formula:
//   sigma_intro_transf(E)[k](u) = (k,u).
injective symbol sigma_intro_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord E (@Const_catd K (@Sigma_cat K E)));

// Component of `sigma_intro_transf` at k.
//
// Surface/formula:
//   sigma_intro_tapp0_func(E,k)(u) = (k,u).
symbol sigma_intro_tapp0_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Fibre_cat E k) (Sigma_cat E));

rule @tapp0_fapp0
      $K Cat_cat $E _ $k (@sigma_intro_transf $K $E)
  ↪ @sigma_intro_tapp0_func $K $E $k;

rule fapp0 (@sigma_intro_tapp0_func $K $E $k) $u
  ↪ Struct_sigma $k $u;

// Generic Pi helper: evaluation transfor from a constant section to a family.
//
// Surface/formula:
//   pi_eval_transf(E)[k] = piapp0_func(E,k).
injective symbol pi_eval_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord
      (@Const_catd K (@Functord_cat K (@Const_catd K Terminal_cat) E))
      E);

rule @tapp0_fapp0
      $K Cat_cat
      (@Const_catd $K (@Functord_cat $K (@Const_catd $K Terminal_cat) $E))
      $E $k
      (@pi_eval_transf $K $E)
  ↪ @piapp0_func $K $E $k;

// Fixed-base layer: constant section constructor.
//
// Surface/formula:
//   const_section_func(K,A)(a) = (k :^n K) ↦ a
//   as an object of Π k :^n K, A.
injective symbol const_section_func (K : Cat) (A : Cat)
  : τ (Functor A (@Pi_cat K (@Const_catd K A)));

rule @fapp0 $A _ (@const_section_func $K $A) $a
  ↪ @Const_func $K $A $a;

rule @fapp1_func $A _ (@const_section_func $K $A) $x $y
  ↪ @Const_transf_func $K $A $x $y;

rule @fapp1_fapp0 $A _ (@const_section_func $K $A) $x $y $p
  ↪ @Const_transf $K $A $x $y $p;

// Pairing telescope for products.
//
// Surface/formula:
//   Product_pair_tele_func(A,B) : A ⊢ (B ⊢ A x B)
//   Product_pair_tele_func[x][y] = (x,y)
//   Product_pair_tele_func[p][y] = (p,id_y).
rule sigma_Fst (@Product_pair_tele_func $A $B)
  ↪ @const_section_func $B $A;

rule sigma_Snd (@Product_pair_tele_func $A $B)
  ↪ @Const_func $A (Functor_cat $B $B) (@id_func $B);

rule @fapp0 $A (Product_cat (Functor_cat $B $A) (Functor_cat $B $B))
      (@Product_pair_tele_func $A $B) $x
  ↪ Struct_sigma (@Const_func $B $A $x) (@id_func $B);

rule @fapp1_func $A (Product_cat (Functor_cat $B $A) (Functor_cat $B $B))
      (@Product_pair_tele_func $A $B) $x $x'
  ↪ Struct_sigma
      (@Const_transf_func $B $A $x $x')
      (@Const_func
        (Hom_cat $A $x $x')
        (@Transf_cat $B $B (@id_func $B) (@id_func $B))
        (@id (Functor_cat $B $B) (@id_func $B)));

rule @fapp1_fapp0 $A (Product_cat (Functor_cat $B $A) (Functor_cat $B $B))
      (@Product_pair_tele_func $A $B) $x $x' $p
  ↪ Struct_sigma
      (@Const_transf $B $A $x $x' $p)
      (@id (Functor_cat $B $B) (@id_func $B));

// Generic full hom-action for identity and composition of ordinary functors.
// These rules let semantic aliases such as curry expose functor-level action
// instead of falling back to capped `fapp1_fapp0` computation only.
rule @fapp1_func $A $A (@id_func $A) $x $y
  ↪ @id_func (Hom_cat $A $x $y);

rule @fapp1_func $A $C (@comp_cat_fapp0 $A $B $C $F $G) $x $y
  ↪ @comp_cat_fapp0
      (Hom_cat $A $x $y)
      (Hom_cat $B
        (@fapp0 $A $B $G $x)
        (@fapp0 $A $B $G $y))
      (Hom_cat $C
        (@fapp0 $B $C $F (@fapp0 $A $B $G $x))
        (@fapp0 $B $C $F (@fapp0 $A $B $G $y)))
      (@fapp1_func
        $B
        $C
        $F
        (@fapp0 $A $B $G $x)
        (@fapp0 $A $B $G $y))
      (@fapp1_func $A $B $G $x $y);

// Semantic curry sanity checks. These live after `Product_pair_tele_func`
// computation rules, because the primary curry package is a definition through
// that telescope rather than a primitive object-action rewrite rule.

// Internalized-x prerequisite: pull a section back along a base functor.
//
// Surface/formula:
//   section_pullback_func(F,E) :
//     (Π b :^n B, E[b]) ⊢ (Π a :^n A, E[F[a]])
//   section_pullback_func(F,E)(s)[a] = s[F[a]].
symbol section_pullback_func [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  : τ (Functor
      (@Functord_cat B (@Const_catd B Terminal_cat) E)
      (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F)));

// Fixed object-level section produced by `section_pullback_func`.
//
// Surface/formula:
//   section_pullback_sec(F,E,s)[a] = s[F[a]].
symbol section_pullback_sec [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Functord_cat B (@Const_catd B Terminal_cat) E)))
  : τ (Obj (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F)));

rule @fapp0 _ _ (@section_pullback_func $A $B $F $E) $s
  ↪ @section_pullback_sec $A $B $F $E $s;

rule @tapp0_fapp0
      $A Cat_cat (@Const_catd $A Terminal_cat) _ $a
      (@section_pullback_sec $A $B $F $E $s)
  ↪ @Obj_func
      (Fibre_cat (@Pullback_catd $A $B $E $F) $a)
      (@piapp0 $B $E $s (@fapp0 $A $B $F $a));

// Internalized-x prerequisite: naturality component of Pi along a base functor.
//
// Surface/formula:
//   section_pullback_transf(F)[E] = section_pullback_func(F,E)
//   : Π b :^n B, E[b] ⊢ Π a :^n A, E[F[a]].
injective symbol section_pullback_transf [A B : Cat]
  (F : τ (Functor A B))
  : τ (Transf
      (@Pi_func B)
      (@comp_cat_fapp0
        (@Catd_cat B)
        (@Catd_cat A)
        Cat_cat
        (@Pi_func A)
        (@Pullback_catd_func A B F)));

rule @tapp0_fapp0
      (@Catd_cat $B)
      Cat_cat
      _
      _
      $E
      (@section_pullback_transf $A $B $F)
  ↪ @section_pullback_func $A $B $F $E;

rule @fdapp1_int_cell
      _
      _
      _
      Pi_int_funcd
      $B
      $A
      $F
      $E
  ↪ @section_pullback_func $A $B $F $E;

rule @fdapp1_int_cell
      $K
      _
      _
      (@Pi_pullback_funcd $K $G)
      $x
      $y
      $p
      $E
  ↪ @section_pullback_func
      (@fapp0 $K (Op_cat Cat_cat) $G $y)
      (@fapp0 $K (Op_cat Cat_cat) $G $x)
      (@fapp1_fapp0 $K (Op_cat Cat_cat) $G $x $y $p)
      $E;

// Internalized-x target layer: target-side path-out transport. The transported
// motive remains canonically `PathOutMotives[p](E)`; this helper exposes its
// pullback presentation so Pi sections move by the generic section-pullback
// map.
//
// Surface/formula:
//   pathout_pi_transport(p,E)
//     : Π q :^n PathOut_Z(x), E[q]
//       ⊢ Π q :^n PathOut_Z(y), E[PathOut_transport(p)[q]].
symbol pathout_pi_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (@Pi_cat (@PathOut_cat Z x) E)
      (@Pi_cat (@PathOut_cat Z y) (@pathout_motive_transport_obj Z x y p E)))
≔ @section_pullback_func
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    E;

// Internalized-x target layer: target transport along the canonical total
// transported-motive arrow.
//
// Surface/formula:
//   PathIndTgt_transport(p,E) = pathout_pi_transport(p,E).
symbol PathIndTgt_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndTgt_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))))
≔ @pathout_pi_transport_func Z x y p E;

/*
  Mathematical computation statements for target transport and the
  source transport over the canonical transported-motive arrow.
*/

// -------------------------------------------------------------------------------------------------
// 16. Remaining constructor/projection assertions
// -------------------------------------------------------------------------------------------------

/*
  The main theorem-like computation statements for path induction,
  target/source transport, and the fixed-x transitivity benchmark live next to
  their motivating declarations above.

  This section keeps lower-level constructor/projection checks and
  dependency-delayed sanity assertions that are still useful as executable
  documentation of canonical normal forms.
*/

/*
  Directed-family constructor normal forms.

  Surface/formula:
    E[k] = Fibre_cat(E,k)
    const_K(A)[k] = A
    1_K[k] = 1
    E^op[k] = E[k]^op
    (F^*E)[a] = E[F[a]].
*/

/*
  Internalized Catd/Pi over varying bases.

  Surface/formula:
    Catd_cat_func[K] = Catd(K)
    Catd_cat_func[F] = F^*
    Pi_int_funcd[K] = Pi_func(K)
    Pi_pullback_funcd(G)[x] = Pi_func(G[x]).
*/

/*
  Section-category and section-evaluation normal forms.

  Surface/formula:
    Pi(E) = Transf(1_K,E)
    Pi(const_K(A)) = K ⊢ A
    Hom_Pi(s,t) = Transfd(s,t)
    s[k] = piapp0(s,k).
*/

// Component of the global internal Pi package at a fixed base.

/*
  Generic Sigma/Pi helper computations.

  Surface/formula:
    sigma_intro(E)[k](u) = (k,u)
    pi_eval(E)[k](s) = s[k]
    const_section_K,A(a)[k] = a
    Obj_func_A(a) = const_section_1,A(a).
*/

/*
  Pullback of sections.

  Surface/formula:
    section_pullback(F,E)(s)[a] = s[F[a]]
    section_pullback_transf(F)[E] = section_pullback(F,E).
*/

/*
  Sigma total category and projection-pullback normal forms.

  Surface/formula:
    Sigma_func(K)[E] = Sigma(E)
    Sigma_map(eta)(k,u) = (k, eta[k](u))
    Sigma_proj1(E)(k,u) = k
    (Sigma_proj1(R))^*D[(k,r)] = D[k]
    Pi_{(k,r):Sigma(R)} D[k] = Functord(R,D).
*/

/*
  Mixed-variance family constructors.

  Surface/formula:
    Functor_catd(M,N)[k] = M[k^-] ⊢_[k] N[k]
    Hom_catd(E,X,Y)[k] = X[k^-] ->_[k]^E Y[k]
    Transf_catd(M,N,FF,GG)[k] = FF[k^-] =>_[k] GG[k]
    Hom_catd(const Cat, X, Y) = Functor_catd(Op_func(X),Y).
*/

// Nested telescope stress example.
//
// Surface/formula:
//   k |-> (z :^n Z ; E[k^-;z] ⊢ D[k;z])
//   = Hom_{Catd(Z)}(E[k^-],D[k]).
symbol Nested_telescope_catd [K Z : Cat]
  (E : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Catd_cat Z))))))
  (D : τ (Obj (Pi_cat (@Const_catd K (@Catd_cat Z)))))
  : τ (Catd K)
≔ @Hom_catd
    K
    (@Const_catd K (@Catd_cat Z))
    E
    D;

// Full nested telescope category:
//   k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z]).
symbol Nested_telescope_cat [K Z : Cat]
  (C : τ (Catd K))
  (E : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Catd_cat Z))))))
  (D : τ (Obj (Pi_cat (@Const_catd K (@Catd_cat Z)))))
  : Cat
≔ @Functord_cat K C (@Nested_telescope_catd K Z E D);

// Nested transformation telescope stress example.
//
// Surface/formula:
//   k |-> (z :^n Z ; FF[k^-;z] => GG[k;z])
//   = Hom_{Functord(E,D)}(FF[k^-],GG[k]).
symbol Nested_transfd_telescope_catd [K Z : Cat]
  (E D : τ (Catd Z))
  (FF : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Functord_cat Z E D))))))
  (GG : τ (Obj (Pi_cat (@Const_catd K (@Functord_cat Z E D)))))
  : τ (Catd K)
≔ @Hom_catd
    K
    (@Const_catd K (@Functord_cat Z E D))
    FF
    GG;

// Full nested transformation telescope category:
//   k :^n K ; C[k] ⊢ (z :^n Z ; FF[k^-;z] => GG[k;z]).
symbol Nested_transfd_telescope_cat [K Z : Cat]
  (C : τ (Catd K))
  (E D : τ (Catd Z))
  (FF : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Functord_cat Z E D))))))
  (GG : τ (Obj (Pi_cat (@Const_catd K (@Functord_cat Z E D)))))
  : Cat
≔ @Functord_cat K C (@Nested_transfd_telescope_catd K Z E D FF GG);

/*
  PathOut category and moving-motive transport.

  Surface/formula:
    Rep_Z(x)[y] = Hom_Z(x,y)
    PathOut_Z(x) = Sigma y :^n Z, Hom_Z(x,y)
    PathOutMotives_Z[x] = Catd(PathOut_Z(x))
    PathOut_Z(p) = precomposition/pullback along p
    pathout_motive_transport(p,E) = PathOut_Z(p)^*E.
*/

/*
  Internalized path-induction source/target fibres.

  Surface/formula:
    PathOutPi_Z[x][E] = Pi(PathOut_Z(x),E)
    PathIndTgt_Z[(x,E)] = Pi(PathOut_Z(x),E)
    PathIndSrc_Z[(x,E)] = E[(x,id_x)]
    PathIndSrc_transport(p,E)(u) = E[rho_{x,y,p}](u).
*/

/*
  Object-level PathOut notation.

  Surface/formula:
    pathout_obj(x;y,p) = (y,p)
    pathout_refl_obj(x) = (x,id_x)
    Sigma_proj1(pathout_obj(x;y,p)) = y
    pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
*/

/*
  Evaluation functors act on transformations by component evaluation.

  Surface/formula:
    fapp0_func(x)[eta] = eta[x]
    pathout_refl_eval_func(x)[eta] = eta[(x,id_x)].
*/

/*
  Covariant fibre transport package.

  Surface/formula:
    FibCov_target(D)[x] = Functord(Rep_Z(x),D)
    fib_cov_int(D)[x](u)[y][f] = D[f](u)
    path_ind_sec(E,u)[(y,p)] = E[rho_{x,y,p}](u).
*/

/*
  Edge, hom-presheaf, and dependent-hom target classifiers.

  Surface/formula:
    Edge_Z(x)[y] = Hom_Z(x,y)^op
    HomPresheaf_Z(x)[y] = Hom_Z(x,y)^op ⊢ Cat
    HomdTargetSection_E[x][y] = E[y^-] ⊢_[y] HomPresheaf_Z(x)[y]
    HomdTarget_E[x] = Π y :^n Z^op, HomdTargetSection_E[x][y].
*/

/*
  Internal covariant transport components.

  Surface/formula:
    FibCov_target(E)[x] = Functord(hom_K(x,-),E)
    fib_cov_src(x)(u) = fib_cov_transf(x,u)
    fib_cov_transf(x,u)[y] = fib_cov_tapp0_func(x,y,u).
*/

/*
  Displayed functor calculus.

  Surface/formula:
    Op_funcd(id_E) = id_{E^op}
    Op_funcd(Op_funcd(FF)) = FF
    (FF o id_E) = FF
    (id_D o GG) = GG
    Fibre_func(FF,z) = FF[z].
*/

/*
  Displayed transfor application packages.

  Surface/formula:
    tdapp1_int_func_transfd(FF,GG)[epsilon] = tdapp1_int_fapp0(epsilon)
    tdapp1_int_fapp0(id_FF) = fdapp1_int_transfd(FF)
    tdapp0_func(z)[epsilon] = epsilon[z]
    Fibre_transf(epsilon,z) = epsilon[z].
*/

/*
  Generic displayed transport routes.

  Surface/formula:
    catd_transport(E,p) = E[p]
    functord_transport(FF,p) = FF[p]
    functord_transport_lhs(FF,p)(u) = D[p](FF[x](u))
    functord_transport_rhs(FF,p)(u) = FF[y](E[p](u))
    Sigma_catd_transport(FF,p,r) = Sigma(FF)[sigma_transport(p,r)].
*/

// Object-level strict naturality of displayed functor transport: both named
// coherence routes compute to the internal off-diagonal component.

/*
  Internal dependent-hom constructor projections.

  Surface/formula:
    homd_int(FF)[x](u) = homd_src_sec(FF,x,u)
    homd_src_sec(FF,x,u)[y] = homd_tgt_func(FF,x,u,y)
    homd_tgt_func(FF,x,u,y)(v) = homd_(FF,x,u,y,v).
*/

// Regression for the `homd_int` first projection. The rule itself keeps the
// source/target family arguments implicit; this assertion may spell them out
// because it is not a rewrite-pattern LHS.

/*
  Terminal-source specializations of the dependent-hom source projection.

  Surface/formula:
    homd_src_func(1,1,id)[x] = constant terminal section
    Fibre_func(homd_int(id_1),x) = that same terminal section.
*/

/*
  Dependent-hom target projection and element computation.

  Surface/formula:
    homd_src_sec(FF,x,u)[y] = homd_tgt_func(FF,x,u,y)
    homd_tgt_func(FF,x,u,y)(v) = homd_(FF,x,u,y,v)
    with the terminal-source case reducing to the displayed Pi-app source.
*/

/*
  End-to-end displayed internal-hom extraction checks.

  The third projection assertion below uses explicit canonical source/target
  slots for `tapp0_fapp0`. The readable form

    tapp0_fapp0 v (fdapp1_int_tgt_arrow ...)

  is mathematically correct but asks Lambdapi to reconstruct too many implicit
  projection parameters and can time out. The `tgt_arrow` head itself is typed
  in reduced `Transf` form; the explicit assertion below is still the robust
  regression surface.
*/

/*
  Constant and terminal dependent-hom specializations.

  Surface/formula:
    homd_(const A, const A, id; x,u,y,v) = const(Hom_A(u,v))
    homd_(1,1,id; x,u,y,v) = terminal
    and their functor/action projections reduce to the same constants.
*/

/*
  Fibre transport and section application source formulas.

  Surface/formula:
    fib_cov_tapp0(const A,x,y,u) = const_{Hom_K(x,y)}(u)
    piapp1_src_obj(s,x,y,f) = E[f](s[x])
    piapp1_fapp0(s,f) = piapp1_func(s)(f).
*/

/*
  Sigma homs and Sigma-map action.

  Surface/formula:
    Hom_Sigma(E)((x,u),(y,v)) = Sigma_{f : Hom_Z(x,y)^op} homd(id_E,x,u,y,v)
    Sigma_map(eta)(k,u) = (k, eta[k](u))
    Sigma_proj1 o Sigma_map(eta) = Sigma_proj1.
*/

// A Sigma map does not preserve canonical transport strictly for arbitrary
// displayed functors. The image exposes the displayed laxity component;
// strict/cartesian preservation is a later specialization.

/*
  Section-dependent-hom composition normal forms.

  Surface/formula:
    (homd_int(s) o Op_funcd(s))[x](*) = homd_src_sec(s,x,s[x])
    evaluating at y and * gives homd_(id_E,x,s[x],y,s[y]).
*/
