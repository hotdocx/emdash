/*
  m- / emdash3.2
  Directed-family mixed-variance v3.2 migration draft.

  This file began as a fork of the retired v3.1 baseline.  It is now the active
  v3.2 development; the v3.1 file and original HOM/FAM/PI/CONST plan are
  archived historical baselines rather than current design authorities.  This file uses
  directed Cat-valued families directly:

    Functor_cat K Cat_cat --> Catd_cat K.
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
      `Functord_cat (Const_catd K Terminal_cat) E`; section homs and
      projections therefore use the displayed-functor normal form directly.
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
    - `catd_transport_func` / `functord_transport_*` /
      `functord_laxity_transf`: generic base-arrow transport,
      naturality-route, and laxity/coherence helpers for displayed functors.
      These are the uniform core counterparts of later path-specific transport
      squares.
    - Pointwise displayed-functor calculus: `Op_funcd` projects through
      `tapp0_fapp0` to ordinary fibre opposites, and `comp_catd_fapp0`
      projects pointwise to ordinary fibre composition. The semantic E/C
      outer-slot form validates; the D/C outer-slot form is not the intended
      general E[x] -> C[x] projection.
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
    Hom_cat(A,x,y)            hom-category Hom_A(x,y), also written x ⟶_A y
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
assert [A : Grpd] ⊢ Obj (Path_cat A) ≡ A;
assert [A : Grpd] (x y : τ A) ⊢ Hom_cat (Path_cat A) x y ≡ Path_cat (x = y);
assert [A : Grpd] (x : τ A) ⊢ @id (Path_cat A) x ≡ eq_refl x;
assert [A : Grpd] (x y z : τ A) (p : τ (x = y)) (q : τ (y = z)) ⊢
  @comp_fapp0 (Path_cat A) x y z q p ≡ eq_trans p q;

// -------------------------------------------------------------------------------------------------
// 2. Ordinary functors and universe categories
// -------------------------------------------------------------------------------------------------

/*
  Ordinary functor category and classifier.

  Surface/formula:
    Functor_cat(A,B)       = A ⟶ B
    Functor(A,B)           = Obj(A ⟶ B)
    F[x]                   = fapp0 F x
    F[X,Y]                 = fapp1_func F : Hom_A(X,Y) -> Hom_B(F[X],F[Y])
    F[f]                   = fapp1_fapp0 F f
*/
injective symbol Functor_cat : Π (A B : Cat), Cat;

injective symbol Functor (A B : Cat) : Grpd
≔ Obj (Functor_cat A B);

unif_rule Obj (Functor_cat $A $B) ≡ Obj (Functor_cat $A' $B') ↪ [ $A ≡ $A'; $B ≡ $B' ];

/*
  Mathematical notation:
    F : A → B                 means F : Functor(A,B)
    F[x]                      = fapp0 F x
    F₁[X,Y]                   = fapp1_func F : Hom_A(X,Y) → Hom_B(F[x],F[y])
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
    Grpd_cat has Obj(Grpd_cat) = Grpd and Hom(X,Y) = X -> Y.
    Cat_cat  has Obj(Cat_cat)  = Cat  and Hom(A,B) = A ⟶ B.
*/
constant symbol Grpd_grpd : Grpd;
constant symbol Cat_grpd  : Grpd;
rule τ Grpd_grpd ↪ Grpd;
rule τ Cat_grpd  ↪ Cat;

// Category of groupoid/type classifiers.
constant symbol Grpd_cat : Cat;
rule Obj Grpd_cat ↪ Grpd_grpd;
rule τ (Obj (Hom_cat Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);

// Category of categories.
constant symbol Cat_cat : Cat;
rule Obj Cat_cat ↪ Cat_grpd;
rule Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;

/*
  Universe-category object and hom computations.

  Surface/formula:
    Obj(Grpd_cat) = Grpd
    Obj(Cat_cat)  = Cat
    Hom_Cat(A,B)  = A -> B.
*/
assert ⊢ τ (Obj Grpd_cat) ≡ Grpd;
assert ⊢ τ (Obj Cat_cat) ≡ Cat;
assert (A B : Cat) ⊢ Hom_cat Cat_cat A B ≡ Functor_cat A B;

// Directed Cat-valued families are canonical Cat-valued functors.
//
// Surface/formula:
//   Catd_cat(K) = K -> Cat
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
//   Functord_cat(E,D) = (k :^n K) -> E[k] ⟶ D[k]
//   Functord(E,D)     = Obj(Functord_cat(E,D)).
injective symbol Functord_cat [K : Cat] (E D : τ (Catd K)) : Cat;

injective symbol Functord [K : Cat] (E D : τ (Catd K)) : Grpd
≔ Obj (@Functord_cat K E D);

unif_rule Obj (@Functord_cat $K $E $D) ≡ Obj (@Functord_cat $K' $E' $D')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D' ];

// `Catd_cat K` is the canonical normal form of `Functor_cat K Cat_cat`.
// Therefore `Hom_cat (Catd_cat K) E D` does not route through a direct
// `Transf_cat K Cat_cat E D` rewrite. The ordinary-functor route
// `Hom_cat (Functor_cat K Cat_cat) E D -> Transf_cat K Cat_cat E D` and the
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
//   Transfd_cat(FF,GG) = (k :^n K) -> FF[k] ⇒ GG[k]
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
    K -> Cat = Catd_cat(K)
    Hom_Catd(E,D) = (k :^n K) -> E[k] -> D[k]
    Hom_Functord(FF,GG) = (k :^n K) -> FF[k] => GG[k].
*/
assert [K : Cat] ⊢ Functor_cat K Cat_cat ≡ Catd_cat K;
assert [K : Cat] (E D : τ (Catd K)) ⊢
  Hom_cat (Catd_cat K) E D ≡ Functord_cat E D;
assert [K : Cat] [E D : τ (Catd K)] (FF GG : τ (Functord E D)) ⊢
  Hom_cat (Functord_cat E D) FF GG ≡ Transfd_cat FF GG;
assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @id (@Functord_cat K E D) FF
    ≡ @id_transfd K E D FF;

/*
  Ordinary identity/composition in Cat_cat.

  Surface/formula:
    id_func(A)             = id_A : A ⟶ A
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
//   Op_func(F) : A^op -> B^op
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
//   Terminal_func(A) : A -> 1
//   Obj_func(y) : 1 -> Y picks out y : Obj(Y).
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
//   Const_func(b) : A -> B
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
//   Obj_func(y) = const_1(y) : 1 -> Y.
injective symbol Obj_func [Y : Cat] (y : τ (Obj Y)) : τ (Functor Terminal_cat Y)
≔ @Const_func Terminal_cat Y y;

// Internalized opposite as a functor in Cat.
//
// Surface/formula:
//   op : Cat -> Cat
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
//   Functor_cat_func[A][B] = A -> B.
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
//   Catd_cat_func : Cat^op -> Cat
//   Catd_cat_func[K] = Catd(K) = (K -> Cat)
//   Catd_cat_func[F : A -> B] = F^* : Catd(B) -> Catd(A)
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
//   comp_cat_cov_func(G) : (X -> Y) -> (X -> Z)
//   comp_cat_cov_func(G)[F] = G ∘ F.
symbol comp_cat_cov_func : Π [X Y Z : Cat],
  Π (G : τ (Functor Y Z)),
  τ (Functor (Functor_cat X Y) (Functor_cat X Z));

rule fapp0 (@comp_cat_cov_func $X $Y $Z $G) $F
  ↪ comp_cat_fapp0 $G $F;

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
    hom_con(W,F)[y]       = Hom_A(F[y],W)
    hom_int(F)[W][y]      = Hom_A(W,F[y])
    hom_precomp_func(f)(g)= g ∘ f

  `hom_int(F)` is the internalized functorial package
  A^op -> (B -> Cat). Its surface reading is:

    W :^f A^op |- y :^f B |- Hom_A(W,y)
*/
injective symbol hom_ [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  : τ (Functor B Cat_cat);
rule @fapp0 $B Cat_cat (@hom_ $A $B $F $W) $y
  ↪ Hom_cat $A $W (@fapp0 $B $A $F $y);

// Ordinary hom-action computes by postcomposition:
// ((Hom_A(W,F-))_1 f)_0 g ↪ (F f) ∘ g.
rule fapp0 (@fapp1_fapp0 $B Cat_cat (@hom_ $A $B $F $W) $X $Y $f) $g
  ↪ comp_fapp0 (fapp1_fapp0 $F $f) $g;

// Contravariant action in the represented object: precompose an arrow
// g : Hom_A(Y,Z) by f : Hom_A(X,Y).
symbol hom_precomp_func [A : Cat] [X Y Z : τ (Obj A)]
  (f : τ (Hom A X Y))
  : τ (Functor (Hom_cat A Y Z) (Hom_cat A X Z));

rule @fapp0 (Hom_cat $A $Y $Z) (Hom_cat $A $X $Z)
      (@hom_precomp_func $A $X $Y $Z $f) $g
  ↪ @comp_fapp0 $A $X $Y $Z $g $f;

// Telescoped internal composition package.
//
// Surface/formula:
//   comp_func_tele(A,x,y,z) :
//     Hom_A(y,z) -> (Hom_A(x,y) -> Hom_A(x,z))
//   comp_func_tele(A,x,y,z)[g][f] = g o f.
symbol comp_func_tele [A : Cat] [X Y Z : τ (Obj A)]
  : τ (Functor
      (Hom_cat A Y Z)
      (Functor_cat (Hom_cat A X Y) (Hom_cat A X Z)))
≔ @fapp1_func
    A
    Cat_cat
    (@hom_ A A (@id_func A) X)
    Y
    Z;

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
//   hom_int(F) : A^op -> (B -> Cat)
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
assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (y : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@hom_ A B F W) y ≡ Hom_cat A W (@fapp0 B A F y);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (x : τ (Obj (Op_cat B))) ⊢
  @fapp0 (Op_cat B) Cat_cat (@hom_con A W B F) x ≡ Hom_cat A (@fapp0 B A F x) W;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj (Op_cat A))) ⊢
  @fapp0 (Op_cat A) (Catd_cat B) (@hom_int A B F) W
    ≡ @hom_ A B F W;

assert [A B : Cat] (F : τ (Functor B A)) (X : τ (Obj (Op_cat A))) (Y : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@fapp0 (Op_cat A) (Catd_cat B) (@hom_int A B F) X) Y
    ≡ Hom_cat A X (fapp0 F Y);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  (X Y : τ (Obj B)) (f : τ (Hom B X Y)) (g : τ (Hom A W (fapp0 F X))) ⊢
  fapp0 (@fapp1_fapp0 B Cat_cat (@hom_ A B F W) X Y f) g
    ≡ @comp_fapp0 A W (fapp0 F X) (fapp0 F Y)
        (fapp0 (@fapp1_func B A F X Y) f) g;

assert [A : Cat] (x y z : τ (Obj A))
  (p : τ (Hom A x y)) (q : τ (Hom A y z)) ⊢
  @fapp0
    (Hom_cat A y z)
    (Hom_cat A x z)
    (@hom_precomp_func A x y z p)
    q
    ≡ @comp_fapp0 A x y z q p;

assert [A : Cat] (x y z : τ (Obj A))
  (p : τ (Hom A x y)) (q : τ (Hom A y z)) ⊢
  @fapp0
    (Hom_cat A x y)
    (Hom_cat A x z)
    (@fapp0
      (Hom_cat A y z)
      (Functor_cat (Hom_cat A x y) (Hom_cat A x z))
      (@comp_func_tele A x y z)
      q)
    p
    ≡ @comp_fapp0 A x y z q p;

assert [A B C : Cat] (F : τ (Functor B C)) (G : τ (Functor A B))
  (x y : τ (Obj A)) (f : τ (Hom A x y)) ⊢
  @fapp1_fapp0
    A
    C
    (@comp_cat_fapp0 A B C F G)
    x
    y
    f
    ≡ @fapp1_fapp0
        B
        C
        F
        (@fapp0 A B G x)
        (@fapp0 A B G y)
        (@fapp1_fapp0 A B G x y f);

assert [A : Cat] (x y : τ (Obj A)) (p : τ (Hom A x y)) ⊢
  @fapp1_fapp0 A A (@id_func A) x y p
    ≡ p;

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

  This is the ordinary/non-dependent warm-up for later dependent
  Sigma-total/comprehension uncurrying. Keep it small until the normal forms
  are stable in v3.2.
*/
injective symbol Product_cat : Π (A B : Cat), Cat;

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

rule Hom_cat (Product_cat $A $B) $p $q
  ↪ Product_cat
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

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

// Universal-property view at object/action level: a functor into a product is
// equivalent to a pair of functors. This is intentionally just the ordinary
// product warm-up; transfor-level product rules can be added later when needed.
symbol Product_projL_func [A B I : Cat]
  (H : τ (Functor I (Product_cat A B)))
  : τ (Functor I A);

symbol Product_projR_func [A B I : Cat]
  (H : τ (Functor I (Product_cat A B)))
  : τ (Functor I B);

injective symbol Product_pair_func [A B I : Cat]
  (F : τ (Functor I A)) (G : τ (Functor I B))
  : τ (Functor I (Product_cat A B));

rule Product_projL_func (Product_pair_func $F $G) ↪ $F
with Product_projR_func (Product_pair_func $F $G) ↪ $G;

rule Product_pair_func (Product_projL_func $H) (Product_projR_func $H) ↪ $H;

rule fapp0 (Product_pair_func $F $G) $i
  ↪ Struct_sigma (fapp0 $F $i) (fapp0 $G $i);

rule fapp0 (Product_projL_func $H) $i
  ↪ sigma_Fst (fapp0 $H $i);

rule fapp0 (Product_projR_func $H) $i
  ↪ sigma_Snd (fapp0 $H $i);

rule @fapp1_func _ _ (Product_pair_func $F $G) $i $j
  ↪ Product_pair_func
      (@fapp1_func _ _ $F $i $j)
      (@fapp1_func _ _ $G $i $j);

rule @fapp1_func _ _ (Product_projL_func $H) $i $j
  ↪ Product_projL_func (@fapp1_func _ _ $H $i $j);

rule @fapp1_func _ _ (Product_projR_func $H) $i $j
  ↪ Product_projR_func (@fapp1_func _ _ $H $i $j);

assert [A B : Cat] (x : τ (Obj A)) (u : τ (Obj B)) ⊢
  @Product_projL A B (@Product_pair A B x u) ≡ x;

assert [A B : Cat] (x : τ (Obj A)) (u : τ (Obj B)) ⊢
  @Product_projR A B (@Product_pair A B x u) ≡ u;

assert [A B : Cat]
  (p q : τ (Obj (Product_cat A B))) ⊢
  @Hom_cat (Product_cat A B) p q
    ≡ @Product_cat
        (Hom_cat A (sigma_Fst p) (sigma_Fst q))
        (Hom_cat B (sigma_Snd p) (sigma_Snd q));

assert [A B : Cat] (x : τ (Obj A)) (u : τ (Obj B)) ⊢
  @id (Product_cat A B) (Struct_sigma x u)
    ≡ @Struct_sigma
        (Obj (Hom_cat A x x))
        (λ _ : τ (Obj (Hom_cat A x x)), Obj (Hom_cat B u u))
        (@id A x)
        (@id B u);

assert [A B : Cat]
  (x y z : τ (Obj A))
  (u v w : τ (Obj B))
  (f : τ (Hom A x y))
  (g : τ (Hom A y z))
  (alpha : τ (Hom B u v))
  (beta : τ (Hom B v w)) ⊢
  @comp_fapp0
    (Product_cat A B)
    (Struct_sigma x u)
    (Struct_sigma y v)
    (Struct_sigma z w)
    (Struct_sigma g beta)
    (Struct_sigma f alpha)
    ≡ @Struct_sigma
        (Obj (Hom_cat A x z))
        (λ _ : τ (Obj (Hom_cat A x z)), Obj (Hom_cat B u w))
        (@comp_fapp0 A x y z g f)
        (@comp_fapp0 B u v w beta alpha);

assert [A B I : Cat]
  (F : τ (Functor I A))
  (G : τ (Functor I B))
  (i : τ (Obj I)) ⊢
  @fapp0 I (Product_cat A B) (@Product_pair_func A B I F G) i
    ≡ @Struct_sigma
        (Obj A)
        (λ _ : τ (Obj A), Obj B)
        (@fapp0 I A F i)
        (@fapp0 I B G i);

assert [A B I : Cat]
  (F : τ (Functor I A))
  (G : τ (Functor I B))
  (i j : τ (Obj I)) ⊢
  @fapp1_func I (Product_cat A B) (@Product_pair_func A B I F G) i j
    ≡ @Product_pair_func
        (Hom_cat A (@fapp0 I A F i) (@fapp0 I A F j))
        (Hom_cat B (@fapp0 I B G i) (@fapp0 I B G j))
        (Hom_cat I i j)
        (@fapp1_func I A F i j)
        (@fapp1_func I B G i j);

// -------------------------------------------------------------------------------------------------
// 5. Ordinary transfors
// -------------------------------------------------------------------------------------------------

/*
  Ordinary transfor/natural-transformation category.

  Surface/formula:
    Transf_cat(F,G) = F ⇒ G
    Transf(F,G)     = Obj(F ⇒ G)

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

/*
  Cat-valued transfors reduce to displayed functors.

  Surface/formula:
    Transf(K,Cat,E,D) = Functord(E,D).
*/
assert [K : Cat] (E D : τ (Catd K)) ⊢
  Hom_cat (Catd_cat K) E D ≡ @Transf_cat K Cat_cat E D;
assert [K : Cat] (E D : τ (Catd K)) ⊢
  Hom_cat (Functor_cat K Cat_cat) E D ≡ @Functord_cat K E D;

// Transformations between point functors from the terminal category are just
// arrows in the target. This bridge keeps terminal-source component projections
// convertible to the corresponding target homs, including surface section-action
// computations.
rule @Transf_cat Terminal_cat $Y
    (@Const_func Terminal_cat $Y $u)
    (@Const_func Terminal_cat $Y $v)
  ↪ Hom_cat $Y $u $v;

/*
  Mathematical notation:
    ϵ : F ⇒ G
    tapp0_func(F,G,Y)         : Transf(F,G) → Hom_B(F[Y],G[Y])
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

// Hom-action of evaluation-at-an-object is component projection.
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
// For f : X -> Y, the displayed functor Hom(Y,F-) -> Hom(X,F-) is
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
assert [A B : Cat] (F : τ (Functor B A))
  (x y : τ (Obj A)) (p : τ (Hom A x y)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0
    B
    Cat_cat
    (@hom_ A B F y)
    (@hom_ A B F x)
    b
    (@fapp1_fapp0 (Op_cat A) (@Catd_cat B) (@hom_int A B F) y x p)
    ≡ @hom_precomp_func A x y (@fapp0 B A F b) p;

// Reserved capped ordinary hom-action surface. It is not used by v3.2 rules
// yet.
//
// Surface/formula:
//   tapp1_fapp0(ϵ,f) : F[X] -> G[Y]
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

// Strict naturality for off-diagonal ordinary transfor components, oriented as
// cut elimination.
//
// Surface/formula:
//   G[g] o epsilon[f] -> epsilon[g o f]
//   epsilon[f] o F[g] -> epsilon[f o g].
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
//   D[p](eta[x](u)) -> eta[p](u)
//   eta[y](E[p](u)) -> eta[p](u).
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

// Ordinary product curry/uncurry scaffold and its first hom-action layer.
//
// Surface/formula:
//   curry(F)[x][y]      = F[(x,y)]
//   uncurry(G)[(x,y)]   = G[x][y]
//
// Status:
//   `curry_func F` and `uncurry_func G` remain stable object-action heads.
//   Their functor-level packages and first hom-actions are installed below.
//   Full adjunction/coherence packaging beyond these beta/action laws remains
//   future work.
symbol curry_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  : τ (Functor A (Functor_cat B C));

symbol curry_fapp0_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  : τ (Functor B C);

rule fapp0 (@curry_func $A $B $C $F) $x
  ↪ @curry_fapp0_func $A $B $C $F $x;

rule fapp0 (@curry_fapp0_func $A $B $C $F $x) $y
  ↪ fapp0 $F (Struct_sigma $x $y);

symbol uncurry_func [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  : τ (Functor (Product_cat A B) C);

rule fapp0 (@uncurry_func $A $B $C $G) (Struct_sigma $x $y)
  ↪ fapp0 (fapp0 $G $x) $y;

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 B C
    (@fapp0 A (Functor_cat B C) (@curry_func A B C F) x)
    y
    ≡ @fapp0 (Product_cat A B) C F (Struct_sigma x y);

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 (Product_cat A B) C
    (@uncurry_func A B C G)
    (Struct_sigma x y)
    ≡ @fapp0 B C (@fapp0 A (Functor_cat B C) G x) y;

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 (Product_cat A B) C
    (@uncurry_func A B C (@curry_func A B C F))
    (Struct_sigma x y)
    ≡ @fapp0 (Product_cat A B) C F (Struct_sigma x y);

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 B C
    (@fapp0 A (Functor_cat B C)
      (@curry_func A B C (@uncurry_func A B C G))
      x)
    y
    ≡ @fapp0 B C (@fapp0 A (Functor_cat B C) G x) y;

// More-internal ordinary product/function currying.
//
// The object-level heads above remain the stable projections:
//
//   curry_func_func[A,B,C][F]   = curry_func(F)
//   uncurry_func_func[A,B,C][G] = uncurry_func(G)
//
// The additional heads expose the ordinary hom-action needed to iterate the
// construction as an omega-functorial package.
symbol curry_inner_fapp1_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  [y y' : τ (Obj B)]
  : τ (Functor
      (Hom_cat B y y')
      (Hom_cat
        C
        (@fapp0 (Product_cat A B) C F (Struct_sigma x y))
        (@fapp0 (Product_cat A B) C F (Struct_sigma x y'))));

rule @fapp1_func _ _ (@curry_fapp0_func $A $B $C $F $x) $y $y'
  ↪ @curry_inner_fapp1_func $A $B $C $F $x $y $y';

rule fapp0 (@curry_inner_fapp1_func $A $B $C $F $x $y $y') $q
  ↪ @fapp1_fapp0
      (Product_cat $A $B)
      $C
      $F
      (Struct_sigma $x $y)
      (Struct_sigma $x $y')
      (Struct_sigma (@id $A $x) $q);

rule @fapp1_fapp0 _ _ (@curry_fapp0_func $A $B $C $F $x) $y $y' $q
  ↪ fapp0 (@curry_inner_fapp1_func $A $B $C $F $x $y $y') $q;

symbol curry_outer_fapp1_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  [x x' : τ (Obj A)]
  : τ (Functor
      (Hom_cat A x x')
      (Transf_cat
        (@curry_fapp0_func A B C F x)
        (@curry_fapp0_func A B C F x')));

symbol curry_outer_transf [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  [x x' : τ (Obj A)]
  (p : τ (Hom A x x'))
  : τ (Transf
      (@curry_fapp0_func A B C F x)
      (@curry_fapp0_func A B C F x'));

rule @fapp1_func _ _ (@curry_func $A $B $C $F) $x $x'
  ↪ @curry_outer_fapp1_func $A $B $C $F $x $x';

rule fapp0 (@curry_outer_fapp1_func $A $B $C $F $x $x') $p
  ↪ @curry_outer_transf $A $B $C $F $x $x' $p;

rule @fapp1_fapp0 _ _ (@curry_func $A $B $C $F) $x $x' $p
  ↪ @curry_outer_transf $A $B $C $F $x $x' $p;

rule @tapp0_fapp0 _ _ _ _ $y
      (@curry_outer_transf $A $B $C $F $x $x' $p)
  ↪ @fapp1_fapp0
      (Product_cat $A $B)
      $C
      $F
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y)
      (Struct_sigma $p (@id $B $y));

symbol uncurry_fapp1_func [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  [x x' : τ (Obj A)]
  [y y' : τ (Obj B)]
  : τ (Functor
      (Hom_cat (Product_cat A B) (Struct_sigma x y) (Struct_sigma x' y'))
      (Hom_cat
        C
        (@fapp0 B C (@fapp0 A (Functor_cat B C) G x) y)
        (@fapp0 B C (@fapp0 A (Functor_cat B C) G x') y')));

rule @fapp1_func _ _ (@uncurry_func $A $B $C $G)
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y')
  ↪ @uncurry_fapp1_func $A $B $C $G $x $x' $y $y';

rule fapp0 (@uncurry_fapp1_func $A $B $C $G $x $x' $y $y')
      (Struct_sigma $p $q)
  ↪ @comp_fapp0
      $C
      (@fapp0 $B $C (@fapp0 $A (Functor_cat $B $C) $G $x) $y)
      (@fapp0 $B $C (@fapp0 $A (Functor_cat $B $C) $G $x') $y)
      (@fapp0 $B $C (@fapp0 $A (Functor_cat $B $C) $G $x') $y')
      (@fapp1_fapp0
        $B
        $C
        (@fapp0 $A (Functor_cat $B $C) $G $x')
        $y
        $y'
        $q)
      (@tapp0_fapp0
        $B
        $C
        (@fapp0 $A (Functor_cat $B $C) $G $x)
        (@fapp0 $A (Functor_cat $B $C) $G $x')
        $y
        (@fapp1_fapp0
          $A
          (Functor_cat $B $C)
          $G
          $x
          $x'
          $p));

rule @fapp1_fapp0 _ _ (@uncurry_func $A $B $C $G)
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y')
      (Struct_sigma $p $q)
  ↪ fapp0
      (@uncurry_fapp1_func $A $B $C $G $x $x' $y $y')
      (Struct_sigma $p $q);

symbol curry_func_func [A B C : Cat]
  : τ (Functor
      (Functor_cat (Product_cat A B) C)
      (Functor_cat A (Functor_cat B C)));

rule fapp0 (@curry_func_func $A $B $C) $F
  ↪ @curry_func $A $B $C $F;

symbol curry_func_fapp1_func [A B C : Cat]
  [F G : τ (Functor (Product_cat A B) C)]
  : τ (Functor
      (Transf_cat F G)
      (Transf_cat
        (@curry_func A B C F)
        (@curry_func A B C G)));

symbol curry_transf [A B C : Cat]
  [F G : τ (Functor (Product_cat A B) C)]
  (eta : τ (Transf F G))
  : τ (Transf
      (@curry_func A B C F)
      (@curry_func A B C G));

symbol curry_transf_tapp0_transf [A B C : Cat]
  [F G : τ (Functor (Product_cat A B) C)]
  (eta : τ (Transf F G))
  (x : τ (Obj A))
  : τ (Transf
      (@curry_fapp0_func A B C F x)
      (@curry_fapp0_func A B C G x));

rule @fapp1_func _ _ (@curry_func_func $A $B $C) $F $G
  ↪ @curry_func_fapp1_func $A $B $C $F $G;

rule fapp0 (@curry_func_fapp1_func $A $B $C $F $G) $eta
  ↪ @curry_transf $A $B $C $F $G $eta;

rule @fapp1_fapp0 _ _ (@curry_func_func $A $B $C) $F $G $eta
  ↪ @curry_transf $A $B $C $F $G $eta;

rule @tapp0_fapp0 _ _ _ _ $x
      (@curry_transf $A $B $C $F $G $eta)
  ↪ @curry_transf_tapp0_transf $A $B $C $F $G $eta $x;

rule @tapp0_fapp0 _ _ _ _ $y
      (@curry_transf_tapp0_transf $A $B $C $F $G $eta $x)
  ↪ @tapp0_fapp0
      (Product_cat $A $B)
      $C
      $F
      $G
      (Struct_sigma $x $y)
      $eta;

symbol uncurry_func_func [A B C : Cat]
  : τ (Functor
      (Functor_cat A (Functor_cat B C))
      (Functor_cat (Product_cat A B) C));

rule fapp0 (@uncurry_func_func $A $B $C) $G
  ↪ @uncurry_func $A $B $C $G;

symbol uncurry_func_fapp1_func [A B C : Cat]
  [G H : τ (Functor A (Functor_cat B C))]
  : τ (Functor
      (Transf_cat G H)
      (Transf_cat
        (@uncurry_func A B C G)
        (@uncurry_func A B C H)));

symbol uncurry_transf [A B C : Cat]
  [G H : τ (Functor A (Functor_cat B C))]
  (theta : τ (Transf G H))
  : τ (Transf
      (@uncurry_func A B C G)
      (@uncurry_func A B C H));

rule @fapp1_func _ _ (@uncurry_func_func $A $B $C) $G $H
  ↪ @uncurry_func_fapp1_func $A $B $C $G $H;

rule fapp0 (@uncurry_func_fapp1_func $A $B $C $G $H) $theta
  ↪ @uncurry_transf $A $B $C $G $H $theta;

rule @fapp1_fapp0 _ _ (@uncurry_func_func $A $B $C) $G $H $theta
  ↪ @uncurry_transf $A $B $C $G $H $theta;

rule @tapp0_fapp0 _ _ _ _ (Struct_sigma $x $y)
      (@uncurry_transf $A $B $C $G $H $theta)
  ↪ @tapp0_fapp0
      $B
      $C
      (@fapp0 $A (Functor_cat $B $C) $G $x)
      (@fapp0 $A (Functor_cat $B $C) $H $x)
      $y
      (@tapp0_fapp0
        $A
        (Functor_cat $B $C)
        $G
        $H
        $x
        $theta);

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  (y y' : τ (Obj B))
  ⊢
  @fapp1_func B C (@curry_fapp0_func A B C F x) y y'
    ≡ @curry_inner_fapp1_func A B C F x y y';

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  (y y' : τ (Obj B))
  (q : τ (Hom B y y')) ⊢
  @fapp1_fapp0 B C (@curry_fapp0_func A B C F x) y y' q
    ≡ @fapp1_fapp0
        (Product_cat A B)
        C
        F
        (Struct_sigma x y)
        (Struct_sigma x y')
        (Struct_sigma (@id A x) q);

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x x' : τ (Obj A))
  ⊢
  @fapp1_func A (Functor_cat B C) (@curry_func A B C F) x x'
    ≡ @curry_outer_fapp1_func A B C F x x';

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x x' : τ (Obj A))
  (p : τ (Hom A x x'))
  (y : τ (Obj B)) ⊢
  @tapp0_fapp0
    B
    C
    (@curry_fapp0_func A B C F x)
    (@curry_fapp0_func A B C F x')
    y
    (@fapp1_fapp0 A (Functor_cat B C) (@curry_func A B C F) x x' p)
    ≡ @fapp1_fapp0
        (Product_cat A B)
        C
        F
        (Struct_sigma x y)
        (Struct_sigma x' y)
        (Struct_sigma p (@id B y));

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x x' : τ (Obj A))
  (y y' : τ (Obj B))
  ⊢
  @fapp1_func
    (Product_cat A B)
    C
    (@uncurry_func A B C G)
    (Struct_sigma x y)
    (Struct_sigma x' y')
    ≡ @uncurry_fapp1_func A B C G x x' y y';

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x x' : τ (Obj A))
  (y y' : τ (Obj B))
  (p : τ (Hom A x x'))
  (q : τ (Hom B y y')) ⊢
  @fapp1_fapp0
    (Product_cat A B)
    C
    (@uncurry_func A B C G)
    (Struct_sigma x y)
    (Struct_sigma x' y')
    (Struct_sigma p q)
    ≡ @comp_fapp0
        C
        (@fapp0 B C (@fapp0 A (Functor_cat B C) G x) y)
        (@fapp0 B C (@fapp0 A (Functor_cat B C) G x') y)
        (@fapp0 B C (@fapp0 A (Functor_cat B C) G x') y')
        (@fapp1_fapp0
          B
          C
          (@fapp0 A (Functor_cat B C) G x')
          y
          y'
          q)
        (@tapp0_fapp0
          B
          C
          (@fapp0 A (Functor_cat B C) G x)
          (@fapp0 A (Functor_cat B C) G x')
          y
          (@fapp1_fapp0
            A
            (Functor_cat B C)
            G
            x
            x'
            p));

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C)) ⊢
  @fapp0
    (Functor_cat (Product_cat A B) C)
    (Functor_cat A (Functor_cat B C))
    (@curry_func_func A B C)
    F
    ≡ @curry_func A B C F;

assert [A B C : Cat]
  (F G : τ (Functor (Product_cat A B) C)) ⊢
  @fapp1_func
    (Functor_cat (Product_cat A B) C)
    (Functor_cat A (Functor_cat B C))
    (@curry_func_func A B C)
    F
    G
    ≡ @curry_func_fapp1_func A B C F G;

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C))) ⊢
  @fapp0
    (Functor_cat A (Functor_cat B C))
    (Functor_cat (Product_cat A B) C)
    (@uncurry_func_func A B C)
    G
    ≡ @uncurry_func A B C G;

assert [A B C : Cat]
  (G H : τ (Functor A (Functor_cat B C))) ⊢
  @fapp1_func
    (Functor_cat A (Functor_cat B C))
    (Functor_cat (Product_cat A B) C)
    (@uncurry_func_func A B C)
    G
    H
    ≡ @uncurry_func_fapp1_func A B C G H;

assert [A B C : Cat]
  (F G : τ (Functor (Product_cat A B) C))
  (eta : τ (Transf F G))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @tapp0_fapp0
    B
    C
    (@curry_fapp0_func A B C F x)
    (@curry_fapp0_func A B C G x)
    y
    (@tapp0_fapp0
      A
      (Functor_cat B C)
      (@curry_func A B C F)
      (@curry_func A B C G)
      x
      (@fapp1_fapp0
        (Functor_cat (Product_cat A B) C)
        (Functor_cat A (Functor_cat B C))
        (@curry_func_func A B C)
        F
        G
        eta))
    ≡ @tapp0_fapp0
        (Product_cat A B)
        C
        F
        G
        (Struct_sigma x y)
        eta;

assert [A B C : Cat]
  (G H : τ (Functor A (Functor_cat B C)))
  (theta : τ (Transf G H))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @tapp0_fapp0
    (Product_cat A B)
    C
    (@uncurry_func A B C G)
    (@uncurry_func A B C H)
    (Struct_sigma x y)
    (@fapp1_fapp0
      (Functor_cat A (Functor_cat B C))
      (Functor_cat (Product_cat A B) C)
      (@uncurry_func_func A B C)
      G
      H
      theta)
    ≡ @tapp0_fapp0
        B
        C
        (@fapp0 A (Functor_cat B C) G x)
        (@fapp0 A (Functor_cat B C) H x)
        y
        (@tapp0_fapp0
          A
          (Functor_cat B C)
          G
          H
          x
          theta);

/*
  More-internal ordinary hom-action.

  This ports the settled v2 core without also committing to the later
  hom-action packaging heads.  The functor sends a transfor ϵ : F ⇒ G to the
  internalized action

    hom_int(id_A) ⇒ hom_int(G) ∘ F^op.

  Surface/formula:
    tapp1_int_func_transf(F,G)[ϵ]
      : Hom_A(~,—) ⇒ Hom_B(F^op ~,G —)

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

/*
  Ordinary internal hom-action package.

  Surface/formula:
    tapp1_int_func_transf(F,G)[epsilon]
      = internal action Hom_A(~,-) => Hom_B(F^op ~, G -)
    fapp1_int_transf(F) is the identity-specialized action.
*/
assert [A B : Cat] (F G : τ (Functor A B)) (ϵ : τ (Transf F G)) ⊢
  fapp0 (@tapp1_int_func_transf A B F G) ϵ
    ≡ @tapp1_int_fapp0_transf A B F G ϵ;

assert [A B : Cat] (F G : τ (Functor A B))
  (ϵ ϵ' : τ (Transf F G)) ⊢
  @fapp1_func _ _ (@tapp1_int_func_transf A B F G) ϵ ϵ'
    ≡ @tapp1_int_fapp1_func_transf A B F G ϵ ϵ';

assert [A B : Cat] (F G : τ (Functor A B))
  (X Y Z : τ (Obj A))
  (f : τ (Hom A X Y))
  (g : τ (Hom A Y Z))
  (ϵ : τ (Transf F G)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@fapp0 A B G Z)
    (@fapp1_fapp0 A B G Y Z g)
    (@tapp1_fapp0 A B F G X Y ϵ f)
    ≡ @tapp1_fapp0 A B F G X Z ϵ
        (@comp_fapp0 A X Y Z g f);

assert [A B : Cat] (F G : τ (Functor A B))
  (X0 X Y : τ (Obj A))
  (g : τ (Hom A X0 X))
  (f : τ (Hom A X Y))
  (ϵ : τ (Transf F G)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F X0)
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@tapp1_fapp0 A B F G X Y ϵ f)
    (@fapp1_fapp0 A B F X0 X g)
    ≡ @tapp1_fapp0 A B F G X0 Y ϵ
        (@comp_fapp0 A X0 X Y f g);

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @tapp1_int_fapp0_transf A B F F (id (Functor_cat A B) F)
    ≡ @fapp1_int_transf A B F;

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  fapp0 (@tapp1_int_func_transf A B F F) (id (Functor_cat A B) F)
    ≡ @fapp1_int_transf A B F;

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
    Pi_cat(E)                 = Π_k E[k]
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
//   F^*E : A -> Cat
//   (F^*E)[a] = E[F[a]]
symbol Pullback_catd [A B : Cat] (E : τ (Catd B)) (F : τ (Functor A B))
  : τ (Catd A)
≔ @comp_cat_fapp0 A B Cat_cat E F;

// Internalized-x prerequisite: generic base-arrow transport for displayed
// Cat-valued families.
//
// Surface/formula:
//   E[p] : E[x] -> E[y]
//   catd_transport_func(E,p) = fapp1_fapp0(E,p)
symbol catd_transport_func [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat E y))
≔ @fapp1_fapp0 K Cat_cat E x y p;

// Strict object transport, oriented as cut elimination.
//
// Surface/formula:
//   E[q](E[p](u)) -> E[q o p](u).
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
//   Pullback_catd_func(F) : (B -> Cat) -> (A -> Cat)
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
//   Pi_cat(E) = Π k :^f K, E[k]
//   section object s has components s[k] : E[k].
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;

rule @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ↪ Functor_cat $K $A;

// Fixed-base layer: functorial section-category constructor at a fixed base.
//
// Surface/formula:
//   Pi_func(K)[E] = Π k :^f K, E[k].
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
//   Pi_int_funcd : (K :^n Cat^op) -> (K -> Cat) -> Cat
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
//   for G : K -> Cat^op,
//   Pi_pullback_funcd(G) : (x :^n K) -> (G[x] -> Cat) -> Cat
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
//   piapp0_func(E,k) : (Π i :^f K, E[i]) -> E[k].
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
//   fib_cov_tapp0_func(E,x,u,y) : Hom_K(x,y) -> E[y]
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
//   homd_(FF,x,u,y,v)[f : x -> y]
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
    Sigma_cat(E)              = Σ_k E[k]
    Obj(Sigma_cat(E))         = Σ (k : Obj K), Obj(E[k])
    Sigma_proj1_func(E)(k,u)  = k
    Sigma_proj1_pullback(R,D) = D pulled back along Sigma_proj1_func(R)
    Π_{(k,r):ΣR} D[k]         = Functord_cat(R,D)
    Sigma_func[K][E]          = Sigma_cat(E)
    sigma_map_func(η)(k,u)    = (k, η_k(u))
*/
// Fixed-base layer: total category of a directed family.
//
// Surface/formula:
//   Sigma_cat(E) = Σ k :^f K, E[k]
//   Obj(Sigma_cat(E)) has objects (k,u).
//
// Current computational status:
//   The Sigma rules below expose object action, capped 1-arrow action
//   (`fapp1_fapp0`), and 1-arrow composition. They are deliberately enough for
//   path/arrow transitivity, total transports, and rho coherence. They are not
//   yet the final full omega-functorial API for `fapp1_func(sigma_map_func eta)`
//   on all higher hom-action data.
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
//   Sigma_proj1_func(E) : Sigma_cat(E) -> K
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
//   sigma_map_func(η) : Sigma_cat(E) -> Sigma_cat(D)
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

// Arrow action of a Sigma map on the canonical Sigma-hom constructor.
//
// Surface/formula:
//   Sigma(eta)[(p,alpha)] = (p, eta[y][alpha]).
//
// This is the capped action `fapp1_fapp0` of `sigma_map_func`. A future
// full-omega layer should expose the corresponding `fapp1_func` package between
// Sigma hom-categories.
//
// The two possible source objects in D[y],
//   D[p](eta[x](u)) and eta[y](E[p](u)),
// are connected by the Cat-valued object-level strict-naturality folds above.
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
      (@fapp1_fapp0
        (Fibre_cat $E $y)
        (Fibre_cat $D $y)
        (@tapp0_fapp0 $K Cat_cat $E $D $y $η)
        (@fapp0
          (Fibre_cat $E $x)
          (Fibre_cat $E $y)
          (@catd_transport_func $K $E $x $y $p)
          $u)
        $v
        $alpha);

rule @comp_cat_fapp0 _ _ _
      (@Sigma_proj1_func $K $D)
      (@sigma_map_func $K $E $D $η)
  ↪ @Sigma_proj1_func $K $E;

// Internalized-x prerequisite: canonical total arrow over a base arrow.
//
// Surface/formula:
//   sigma_transport_arrow(E,p,u) : (x,u) -> (y,E[p](u))
//   in Sigma_cat(E) = Σ k :^f K, E[k].
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
//   if FF : (k :^n K) -> R[k] -> Cat, then
//   Sigma_catd_functord_catd(FF) : (Σ k :^f K, R[k]) -> Cat
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
//     : FF[x][r] -> FF[y][R[p](r)]
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
    Functor_catd(A,B)[k]      = A[k^-] ⟶ B[k]
    Functor_catd_func(K)[A][B]= Functor_catd(A,B)
    Hom_catd(E,X,Y)[k]        = Hom_{E[k]}(X[k^-],Y[k])
    Transf_catd(A,B,FF,GG)[k] = FF[k^-] ⇒ GG[k]
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
//   Hom_catd(E,X,Y)[k] = Hom_{E[k]}(X[k^-],Y[k]).
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
//   Transf_catd(A,B,FF,GG)[k] = FF[k^-] ⇒ GG[k].
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

assert [Z : Cat] (x y z : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Rep_catd Z y)
    (@Rep_catd Z x)
    z
    (@fapp1_fapp0 (Op_cat Z) (@Catd_cat Z) (@Rep_catd_func Z) y x p)
    ≡ @hom_precomp_func Z x y z p;

// Fixed-x layer: outgoing-path category at a fixed source object.
//
// Surface/formula:
//   PathOut_Z(x) = Σ y :^f Z, Hom_Z(x,y)
//   object notation: (y,p) with p : Hom_Z(x,y).
symbol PathOut_cat [Z : Cat] (x : τ (Obj Z)) : Cat
≔ @Sigma_cat Z (@Rep_catd Z x);

// Internalized-x layer: PathOut as a contravariant functor of the source.
//
// Surface/formula:
//   PathOut_cat_func(Z) : Z^op -> Cat
//   PathOut_cat_func(Z)[x] = PathOut_Z(x)
//   PathOut_cat_func(Z)[p : x -> y] : PathOut_Z(y) -> PathOut_Z(x).
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
//   : PathOut_Z(y) -> PathOut_Z(x)
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
//   i.e. a fibre object E is a motive E : PathOut_Z(x) -> Cat.
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
//   PathOutPi_Z : (x :^n Z) -> Catd(PathOut_Z(x)) -> Cat
//   PathOutPi_Z[x][E] = Π q :^f PathOut_Z(x), E[q].
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
//   PathIndTgt_Z[(x,E)] = Π q :^f PathOut_Z(x), E[q]
//   over Σ x :^f Z, Catd(PathOut_Z(x)).
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
//   PathOutReflEval_Z : (x :^n Z) -> Catd(PathOut_Z(x)) -> Cat
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
//   rho_{x,y,p} : (x,id_x) -> (y,p) in PathOut_Z(x).
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
//   E[rho_{x,y,p}] : E[(x,id_x)] -> E[(y,p)].
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
//   so p_*E : PathOut_Z(y) -> Cat.
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
// Σ x :^f Z, Catd(PathOut_Z(x)).
//
// Surface/formula:
//   (x,E) -> (y,p_*E), lying over p : x -> y.
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
//   path_ind_sec(x,E,u) : Π q :^f PathOut_Z(x), E[q]
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
//     Π q :^f PathOut_Z(x), Hom_{PathOut_Z(x)}((x,id_x),q)
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
//   PathInd_tgt(Z,x)[E] = Π q :^f PathOut_Z(x), E[q].
symbol PathInd_tgt_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@Catd_cat (@PathOut_cat Z x)))
≔ @Pi_func (@PathOut_cat Z x);

// Fixed-x internal layer: component functor of the fixed-source eliminator.
//
// Surface/formula:
//   path_ind_func_fapp0(Z,x,E) : E[(x,id_x)] -> Π q, E[q]
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
//     (E :^n Catd(PathOut_Z(x))) -> E[(x,id_x)] -> Π q, E[q].
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
//     (x :^n Z) -> PathOutReflEval_Z[x] => PathOutPi_Z[x]
//   PathInd_transfd(Z)[x] = PathInd_func(Z,x).
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
//   over Σ x :^f Z, Catd(PathOut_Z(x)).
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
//   : E[(x,id_x)] -> (p_*E)[(y,id_y)] = E[(y,p)].
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
//     (x,E :^n Σ x :^f Z, Catd(PathOut_Z(x))) ->
//       E[(x,id_x)] -> Π q :^f PathOut_Z(x), E[q]
//   PathInd_funcd(Z)[(x,E)][u] = path_ind_sec(Z,x,E,u).
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
assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathInd_src_catd Z x) E
    ≡ Fibre_cat E (@pathout_refl_obj Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @PathInd_src_catd Z x
    ≡ @pathout_refl_eval_func Z x;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathInd_tgt_catd Z x) E
    ≡ Pi_cat E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@path_ind_func_fapp0 Z x E)
    u
    ≡ @path_ind_sec Z x E u;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@PathInd_src_catd Z x)
    (@PathInd_tgt_catd Z x)
    E
    (@PathInd_func Z x)
    ≡ @path_ind_func_fapp0 Z x E;

// Transitivity benchmark layer: target family for composition out of a fixed
// source x.
//
// Surface/formula:
//   CompTarget_Z(x)[y] = Rep_Z(y) -> Rep_Z(x)
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
//   CompTarget_Z(x)[p : a -> b]
//     : (Rep_Z(a) -> Rep_Z(x)) -> (Rep_Z(b) -> Rep_Z(x)).
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
//   CompMotive_Z(x)[(y,p)] = Rep_Z(y) -> Rep_Z(x).
//
// This is the pullback of `CompTarget_Z(x)` along the Sigma projection
// PathOut_Z(x) -> Z.
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
//   Presheaf_catd(K)[A][k] = A[k] -> Cat.
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
//   HomPresheaf_Z(x)[y] = Hom_Z(x,y)^op -> Cat.
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
    HomdTargetSection_E(x)(y) = Functor_cat(E[y], HomPsh_Z(x)(y))
    HomdTarget_E[x]           = Pi_y HomdTargetSection_E(x)(y)

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
//   HomdTarget_E[x] = Π y :^f Z^op, E[y^-] -> HomPsh_Z(x)[y].
symbol Homd_target_catd [Z : Cat] (E : τ (Catd Z))
  : τ (Catd Z)
≔ comp_cat_fapp0
     (comp_cat_fapp0
       (@Pi_func (Op_cat Z))
       (fapp0 (@Functor_catd_func (Op_cat Z)) E))
     (@HomPresheaf_catd_func Z);

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_catd Z E) x
    ≡ Pi_cat (@Homd_target_section_catd Z E x);

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
    fib_cov_int(E)               : E → FibCovTarget_E
    fib_cov_src_func(E,x)        : E[x] → FibCovTarget_E[x]
    fib_cov_transf(E,x,u)        : hom_Z(x,-) ⇒ E
                                  ≡ Functord(hom_Z(x,-), E)
    fib_cov_tapp0_func(E,x,u,y)  : Hom_Z(x,y) → E[y]
    fib_cov_tapp0_func(E,x,u,y)(f) = E(f)(u)

  Locally, `→` denotes an ordinary functor and `⇒` denotes the mathematical
  transfor/natural-transformation reading. In the formal v3.2 normal form, a
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
//   fib_cov_int(E)[x](u) : Rep_K(x) -> E
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
assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_ind_sec
    Z
    x
    (@Sigma_proj1_pullback_catd Z (@Rep_catd Z x) D)
    u
    ≡ @fib_cov_transf Z D x u;

// Final desired transitivity benchmark theorem/object.
//
// Surface/formula:
//   path_comp_sec(x) :
//     (p :^n Rep_Z(x)[y]) -> Rep_Z(y) -> Rep_Z(x)
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
//   path_comp_func(p) : Rep_Z(y) -> Rep_Z(x)
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
assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  Fibre_cat (@CompTarget_catd Z x) y
    ≡ @Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  Fibre_cat (@CompMotive_catd Z x) (@pathout_obj Z x y p)
    ≡ @Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x)
    ≡ @Functord_cat Z (@Rep_catd Z x) (@CompTarget_catd Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @path_ind_sec
    Z
    x
    (@CompMotive_catd Z x)
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  @fapp1_fapp0
    Z
    Cat_cat
    (@CompTarget_catd Z x)
    x
    y
    p
    ≡ @CompTarget_fapp1_func Z x x y p;

assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  @fapp0
    (@Functord_cat Z (@Rep_catd Z x) (@Rep_catd Z x))
    (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
    (@CompTarget_fapp1_func Z x x y p)
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_func Z x y p;

// The semantic `hom_con` presentation of `CompTarget_catd` computes without a
// CompTarget-specific identity shortcut.
assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  fapp0
    (@fapp1_fapp0
      Z
      Cat_cat
      (@hom_con
        (@Catd_cat Z)
        (@Rep_catd Z x)
        (Op_cat Z)
        (@Rep_catd_func Z))
      x
      y
      p)
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_func Z x y p;

assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  @fapp0
    (Hom_cat Z x y)
    (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
    (@fib_cov_tapp0_func
      Z
      (@CompTarget_catd Z x)
      x
      y
      (@id_funcd Z (@Rep_catd Z x)))
    p
    ≡ @path_comp_func Z x y p;

assert [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y)) ⊢
  @fapp0
    (Hom_cat Z x y)
    (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z x)
      (@CompTarget_catd Z x)
      y
      (@path_comp_sec Z x))
    p
    ≡ @path_comp_func Z x y p;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@path_comp_func Z x y p))
    q
    ≡ @comp_fapp0 Z x y z q p;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@fapp0
        (Hom_cat Z x y)
        (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
        (@tapp0_fapp0
          Z
          Cat_cat
          (@Rep_catd Z x)
          (@CompTarget_catd Z x)
          y
          (@path_comp_sec Z x))
        p))
    q
    ≡ @comp_fapp0 Z x y z q p;

/*
  Internal dependent-hom projection cascade:

    homd_int(FF) at x               -> homd_src_func(FF,x)
    homd_src_func(FF,x) at u        -> homd_src_sec(FF,x,u)
    homd_src_sec(FF,x,u) at y       -> homd_tgt_func(FF,x,u,y)
    homd_tgt_func(FF,x,u,y) at v    -> homd_(FF,x,u,y,v)

  The identity-specialized compatibility heads from v3.1/v3.2 migration have
  been retired; identity cases are written with `FF := id_funcd E`.
*/

// General first projection of `homd_int`: externalize x and the source fibre
// object in E, while the probe family D remains internal.
//
// Surface/formula:
//   homd_src_func(FF,x) : E[x]^op -> Π y :^f Z^op, ...
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
  Full section action over a base arrow.

  Mathematical notation:
    s[x]                      = piapp0 s x
    s[f]                      = piapp1_fapp0 s f : E(f)(s[x]) → s[y]
    piapp1_func(s,x,y)[f]     = s[f]
    piapp1_src_obj(s,f)       = E(f)(s[x])

  `piapp1_func` is the section-level package over the base-arrow category.
  The capped object component is defined by ordinary section evaluation, so it
  remains iterable through `Pi_cat` rather than becoming only an object-level
  shortcut. `piapp1_src_obj` names the reduced source endpoint of that component;
  `piapp1_fapp0` uses it in its displayed hom type. The terminal-specialization
  fold from displayed internal action is installed after the displayed component
  projections, where the stable `tdapp0_fapp0` head is available.
*/
symbol piapp1_src_obj [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Obj (Fibre_cat E y))
≔ fapp0 (@fib_cov_tapp0_func K E x y (@piapp0 K E s x)) f;

// Section action over a hom object.
//
// Surface/formula:
//   piapp1_func(s,x,y)[f] = s[f].
symbol piapp1_func [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  : τ (Obj (Pi_cat
      (homd_
        (@id_funcd K E)
        x (@piapp0 K E s x)
        y (@piapp0 K E s y))));

// Capped section action over a base arrow.
//
// Surface/formula:
//   piapp1_fapp0(s,f) = s[f] : E[f](s[x]) -> s[y].
symbol piapp1_fapp0 [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Hom
      (Fibre_cat E y)
      (@piapp1_src_obj K E s x y f)
      (@piapp0 K E s y))
≔ piapp0 (@piapp1_func K E s x y) f;

rule fapp0 (@piapp1_func $K (@Const_catd $K $A) $s $x $y) $f
  ↪ @fapp1_fapp0 $K $A $s $x $y $f;

// -------------------------------------------------------------------------------------------------
// 13. Internal displayed hom-action heads
// -------------------------------------------------------------------------------------------------

/*
  Mathematical notation:
    tdapp1_int_func_transfd(FF,GG)
      : Transfd(FF,GG) → Transfd(homd_int(id_E), homd_int(GG) ∘ FF^op)

    tdapp1_int_fapp0_transfd(ϵ)
      = the internal displayed hom-action of ϵ

    fdapp1_int_transfd(FF)
      = tdapp1_int_fapp0_transfd(id_FF)

  Current laxity architecture:

    internal hom-action  ->  extracted laxity  ->  Sigma action consumes laxity.

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

    D[p](FF[x](u)) -> FF[y](E[p](u)).

  Once that extraction is stable, `functord_laxity_transf(FF,p)` below should
  be defined or folded from it, and Sigma-map arrow action should consume the
  resulting laxity prefix. Strict constructors will then need explicit folds
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

    Fibre_func(FF,z)          = FF[z] : E[z] → D[z]
    tdapp0_func(z)            : Transfd(FF,GG) → Transf(FF[z],GG[z])
    tdapp0_fapp0(z,ϵ)         = ϵ_z : FF[z] ⇒ GG[z]
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
assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tdapp0_fapp0
    Z
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    (@PathOutReflEval_funcd Z)
    (@PathOutPi_funcd Z)
    x
    (@PathInd_transfd Z)
    ≡ @PathInd_func Z x;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@PathInd_src_catd Z x)
    (@PathInd_tgt_catd Z x)
    E
    (@tdapp0_fapp0
      Z
      (@PathOutMotives_catd Z)
      (@Const_catd Z Cat_cat)
      (@PathOutReflEval_funcd Z)
      (@PathOutPi_funcd Z)
      x
      (@PathInd_transfd Z))
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@tapp0_fapp0
      (@Catd_cat (@PathOut_cat Z x))
      Cat_cat
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x)
      E
      (@tdapp0_fapp0
        Z
        (@PathOutMotives_catd Z)
        (@Const_catd Z Cat_cat)
        (@PathOutReflEval_funcd Z)
        (@PathOutPi_funcd Z)
        x
        (@PathInd_transfd Z)))
    u
    ≡ @path_ind_sec Z x E u;

// First transitivity benchmark rerouted through the synthetic/telescope
// theorem component.
assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0
    (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
    (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
    (@tapp0_fapp0
      (@Catd_cat (@PathOut_cat Z x))
      Cat_cat
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x)
      (@CompMotive_catd Z x)
      (@tdapp0_fapp0
        Z
        (@PathOutMotives_catd Z)
        (@Const_catd Z Cat_cat)
        (@PathOutReflEval_funcd Z)
        (@PathOutPi_funcd Z)
        x
        (@PathInd_transfd Z)))
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

// Fully expanded transitivity benchmark through the synthetic/telescope
// theorem component.
assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@fapp0
        (Hom_cat Z x y)
        (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
        (@tapp0_fapp0
          Z
          Cat_cat
          (@Rep_catd Z x)
          (@CompTarget_catd Z x)
          y
          (@fapp0
            (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
            (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
            (@tapp0_fapp0
              (@Catd_cat (@PathOut_cat Z x))
              Cat_cat
              (@PathInd_src_catd Z x)
              (@PathInd_tgt_catd Z x)
              (@CompMotive_catd Z x)
              (@tdapp0_fapp0
                Z
                (@PathOutMotives_catd Z)
                (@Const_catd Z Cat_cat)
                (@PathOutReflEval_funcd Z)
                (@PathOutPi_funcd Z)
                x
                (@PathInd_transfd Z)))
            (@id_funcd Z (@Rep_catd Z x))))
        p))
    q
    ≡ @comp_fapp0 Z x y z q p;

/*
  Generic Sigma-total uncurrying and the path-induction specialization.

  Surface/formula:
    Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r]
    PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E).
*/
assert [K : Cat] (R : τ (Catd K))
  (S T : τ (Functord R (@Const_catd K Cat_cat)))
  (eta : τ (Transfd S T))
  (k : τ (Obj K))
  (r : τ (Obj (Fibre_cat R k))) ⊢
  @tapp0_fapp0
    (@Sigma_cat K R)
    Cat_cat
    (@Sigma_catd_functord_catd K R S)
    (@Sigma_catd_functord_catd K R T)
    (Struct_sigma k r)
    (@Sigma_transfd_funcd K R S T eta)
    ≡ @tapp0_fapp0
        (Fibre_cat R k)
        Cat_cat
        (@Fibre_func K R (@Const_catd K Cat_cat) S k)
        (@Fibre_func K R (@Const_catd K Cat_cat) T k)
        r
        (@tdapp0_fapp0
          K
          R
          (@Const_catd K Cat_cat)
          S
          T
          k
          eta);

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Sigma_cat Z (@PathOutMotives_catd Z))
    Cat_cat
    (@PathIndSrc_catd Z)
    (@PathIndTgt_catd Z)
    (Struct_sigma x E)
    (@PathInd_funcd Z)
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@tapp0_fapp0
      (@Sigma_cat Z (@PathOutMotives_catd Z))
      Cat_cat
      (@PathIndSrc_catd Z)
      (@PathIndTgt_catd Z)
      (Struct_sigma x E)
      (@PathInd_funcd Z))
    u
    ≡ @path_ind_sec Z x E u;

// Sigma-total presentation of the transitivity benchmark, using the derived
// `PathInd_funcd` component rather than the telescope component directly.
assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0
    (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
    (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
    (@tapp0_fapp0
      (@Sigma_cat Z (@PathOutMotives_catd Z))
      Cat_cat
      (@PathIndSrc_catd Z)
      (@PathIndTgt_catd Z)
      (Struct_sigma x (@CompMotive_catd Z x))
      (@PathInd_funcd Z))
    (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

// Fully expanded transitivity benchmark through the Sigma-total presentation.
assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0
      Z
      Cat_cat
      (@Rep_catd Z y)
      (@Rep_catd Z x)
      z
      (@fapp0
        (Hom_cat Z x y)
        (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
        (@tapp0_fapp0
          Z
          Cat_cat
          (@Rep_catd Z x)
          (@CompTarget_catd Z x)
          y
          (@fapp0
            (Fibre_cat (@CompMotive_catd Z x) (@pathout_refl_obj Z x))
            (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
            (@tapp0_fapp0
              (@Sigma_cat Z (@PathOutMotives_catd Z))
              Cat_cat
              (@PathIndSrc_catd Z)
              (@PathIndTgt_catd Z)
              (Struct_sigma x (@CompMotive_catd Z x))
              (@PathInd_funcd Z))
            (@id_funcd Z (@Rep_catd Z x))))
        p))
    q
    ≡ @comp_fapp0 Z x y z q p;

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
//   pi_hom_fapp0(eta,k) = eta[k] : s[k] -> t[k]
//   for eta : Hom_{Π i :^f K, E[i]}(s,t).
//
// Faithful surface syntax:
//   eta[k] : s[k] -> t[k].
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
//   FF[p] : E[x] -> D[y]
//   for FF : (k :^n K) -> E[k] -> D[k] and p : x -> y.
symbol functord_transport_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y))
≔ @tapp1_fapp0 K Cat_cat E D x y FF p;

// Internalized-x coherence route: first apply FF at x, then transport in D.
//
// Surface/formula:
//   D[p] ∘ FF[x] : E[x] -> D[y].
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
//   FF[y] ∘ E[p] : E[x] -> D[y].
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

// Internalized-x laxity/coherence projection for a displayed functor over a
// base arrow.
//
// Surface/formula:
//   laxity(FF,p) : D[p] o FF[x] => FF[y] o E[p].
//
// This is the explicit skew comparison between the two route functors. It is
// currently an interim stable projection interface: the intended final
// implementation should derive it from the internal displayed hom-action
// (`fdapp1_int_transfd`) applied to canonical/cartesian dependent-hom
// triangles. Sigma-map action should later consume this laxity prefix; it
// should not be the primitive source of the same laxity.
symbol functord_laxity_transf [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (@Transf
      (Fibre_cat E x)
      (Fibre_cat D y)
      (@functord_transport_lhs_func K E D FF x y p)
      (@functord_transport_rhs_func K E D FF x y p));

// Component-level extraction from the current Sigma-total action. This names
// the fibre component of Sigma(FF) applied to the canonical total transport
// arrow. It is deliberately separate from `functord_laxity_transf`: the current
// `sigma_map_func` action exposes the fibre functor action on the canonical
// homd triangle, while Pi laxity needs the nontrivial component extracted from
// internal hom-action.
symbol sigma_map_transport_fibre_arrow [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat D y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y p)
        u)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_rhs_func K E D FF x y p)
        u))
≔ sigma_Snd (@sigma_map_transport_arrow K E D FF x y p u);

// Source dependent-hom section used by the internal-hom extraction.
//
// Mathematical notation:
//   homd_id_src_sec(E,x,u)
//     = homd_int(id_E)[x](u)
//     : Π y :^f K^op, E[y^-] -> Hom_K(x,y)^op -> Cat.
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
//     : Π y :^f K^op, E[y^-] -> Hom_K(x,y)^op -> Cat.
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
//     homd_int(id_E)[x](u) -> homd_int(FF)[x](FF[x](u)).
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u] :
//     Homd_E(x,u,—,—) -> Homd_D(x,FF[x](u),—,FF[—](—)).
//
// Further projections at y, at the transported object E[p](u), and at the base
// arrow p should eventually produce the component of
// `functord_laxity_transf(FF,p)` at u.
symbol functord_laxity_fdapp1_section_arrow [K : Cat] [E D : τ (Catd K)]
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
  ↪ @functord_laxity_fdapp1_section_arrow $K $E $D $FF $x $u;

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
//       -> homd_int(FF)[x](FF[x](u))[y].
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y] :
//     Homd_E(x,u,y,—) => Homd_D(x,FF[x](u),y,FF[y](—)).
//
// The type is written in the reduced `Transf` form because the next projection
// consumes it through `tapp0_fapp0`. This still keeps the codomain functor in
// the canonical `(x -> y)^op -> Cat` form, avoiding the reducible
// `Fibre_cat(HomPresheaf_Z(x),y)` classifier pipeline.
symbol functord_laxity_fdapp1_tgt_arrow [K : Cat] [E D : τ (Catd K)]
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
        (@functord_laxity_fdapp1_section_arrow $K $E $D $FF $x $u))
  ↪ @functord_laxity_fdapp1_tgt_arrow $K $E $D $FF $x $u $y;

// Third projection stage: evaluate the y-component at a fibre object v.
//
// Mathematical notation:
//   fdapp1_section(FF,x,u)[y][v] :
//     homd_int(id_E)[x](u)[y](v)
//       -> homd_int(FF)[x](FF[x](u))[y](v).
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y,v] :
//     Hom_E(E[—](u),v) => Hom_D(D[—](FF[x](u)),FF[y](v)).
//
// The ambient category is written directly as `(x -> y)^op -> Cat`, rather
// than through `Fibre_cat(HomPresheaf_Z(x),y)`. This is the canonical endpoint
// category of the HomPresheaf classifier and avoids making later projections
// depend on unfolding the whole classifier pipeline.
symbol functord_laxity_fdapp1_presheaf_arrow [K : Cat] [E D : τ (Catd K)]
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
      (@functord_laxity_fdapp1_tgt_arrow $K $E $D $FF $x $u $y)
  ↪ @functord_laxity_fdapp1_presheaf_arrow $K $E $D $FF $x $u $y $v;

// Fourth projection stage, with endpoints written directly through `homd_`.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,v][p] :
//     homd_(id_E,x,u,y,v)[p]
//       -> homd_(FF,x,FF[x](u),y,v)[p].
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y,v][p].
//
// This deliberately keeps the endpoints at the stable `homd_` layer. A later
// fold/assertion can expose the simplified fibre-hom category
// `Hom_{D[y]}(D[p](FF[x](u)),FF[y](v))` when a theorem needs that shape.
symbol functord_laxity_fdapp1_hom_func [K : Cat] [E D : τ (Catd K)]
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
      (@functord_laxity_fdapp1_presheaf_arrow $K $E $D $FF $x $u $y $v)
  ↪ @functord_laxity_fdapp1_hom_func $K $E $D $FF $x $y $p $u $v;

// Raw canonical-triangle cell extracted from the internal displayed hom-action.
// This is the stable normal form for a component of `functord_laxity_transf`.
// The concrete transported-object identity first folds to the stable
// `homd_id_canonical_triangle` head below, then this action consumes that head.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,E[p]u][p](id)
//     : D[p](FF[x](u)) -> FF[y](E[p](u)).
//
// Faithful surface syntax:
//   fdapp1_int(FF)[x,u][y,E[p]u][p](id).
symbol functord_laxity_fdapp1_cell [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat D y)
      (fapp0 (functord_transport_lhs_func FF p) u)
      (fapp0 (functord_transport_rhs_func FF p) u));

rule @tapp0_fapp0
      _
      _
      _
      _
      $u
      (@functord_laxity_transf $K $E $D $FF $x $y $p)
  ↪ @functord_laxity_fdapp1_cell $K $E $D $FF $x $y $p $u;

// Canonical source triangle, typed in the direct `homd_` endpoint.
//
// Mathematical notation:
//   id_{E[p](u)} : homd_(id_E,x,u,y,E[p](u))[p].
//
// Faithful surface syntax:
//   id : Homd_E(x,u,y,E[p]u)[p].
//
// This is a stable identity-specialization head, similar in role to `id_func`
// and `id_funcd`: it names the canonical/cartesian triangle. The rewrite below
// folds only the primitive projection normal form `id_{E[p](u)}` to this head,
// not arbitrary identities in arbitrary fibre categories.
constant symbol homd_id_canonical_triangle [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj
      (fapp0
        (homd_
          (@id_funcd K E)
          x
          u
          y
          (fapp0 (catd_transport_func E p) u))
        p));

rule @id
      (@fapp0 $K Cat_cat $E $y)
      (fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $p) $u)
  ↪ @homd_id_canonical_triangle $K $E $x $y $p $u;

rule fapp0
      (@functord_laxity_fdapp1_hom_func $K $E $D $FF $x $y $p $u _)
      (@homd_id_canonical_triangle $K $E $x $y $p $u)
  ↪ @functord_laxity_fdapp1_cell $K $E $D $FF $x $y $p $u;

// -------------------------------------------------------------------------------------------------
// 15. Generic Sigma/Pi weakening helpers
// -------------------------------------------------------------------------------------------------

/*
  Generic Sigma/Pi weakening/evaluation helpers.

    sigma_intro_transf(E)             : E → const(ΣE)
    sigma_intro_tapp0_func(E,k)       : E[k] → ΣE
    sigma_intro_tapp0_func(E,k)(u)    = (k,u)

    pi_eval_transf(E)                 : const(ΠE) → E
    pi_eval_transf(E)[k]              = piapp0_func(E,k) : ΠE → E[k]

    const_section_func(K,A)           : A → Π_k A
    const_section_func(K,A)(a)        = const(a)

    section_pullback_func(F,E)        : Π_B E → Π_A F^*E
    section_pullback_func(F,E)(s)(a)  = s(Fa)

  The arrow action of `sigma_intro_tapp0_func` is intentionally deferred. It
  should eventually send a fibre arrow α : u → v in E[k] to the corresponding
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
//   const_section_func(K,A)(a) = (k :^f K) ↦ a
//   as an object of Π k :^f K, A.
injective symbol const_section_func (K : Cat) (A : Cat)
  : τ (Functor A (@Pi_cat K (@Const_catd K A)));

rule @fapp0 $A _ (@const_section_func $K $A) $a
  ↪ @Const_func $K $A $a;

// Internalized-x prerequisite: pull a section back along a base functor.
//
// Surface/formula:
//   section_pullback_func(F,E) :
//     (Π b :^f B, E[b]) -> (Π a :^f A, E[F[a]])
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
//   : Π b :^f B, E[b] -> Π a :^f A, E[F[a]].
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

rule @functord_laxity_fdapp1_cell
      _
      _
      _
      Pi_int_funcd
      $B
      $A
      $F
      $E
  ↪ @section_pullback_func $A $B $F $E;

rule @functord_laxity_fdapp1_cell
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

// Pi is contravariantly natural in the base category. In the displayed-family
// view, this is the laxity/coherence projection of `Pi_int_funcd` along a base
// arrow `F : A -> B`, seen as `B -> A` in `Op(Cat)`.
rule @functord_laxity_transf
      _
      _
      _
      Pi_int_funcd
      $B
      $A
      $F
  ↪ @section_pullback_transf $A $B $F;

// Pulling `Pi_int_funcd` back along `G : K -> Cat^op` preserves the same Pi
// laxity component along each base arrow p.
rule @functord_laxity_transf
      $K
      _
      _
      (@Pi_pullback_funcd $K $G)
      $x
      $y
      $p
  ↪ @section_pullback_transf
      (@fapp0 $K (Op_cat Cat_cat) $G $y)
      (@fapp0 $K (Op_cat Cat_cat) $G $x)
      (@fapp1_fapp0 $K (Op_cat Cat_cat) $G $x $y $p);

// Internalized-x target layer: target-side path-out transport. The transported
// motive remains canonically `PathOutMotives[p](E)`; this helper exposes its
// pullback presentation so Pi sections move by the generic section-pullback
// map.
//
// Surface/formula:
//   pathout_pi_transport(p,E)
//     : Π q :^f PathOut_Z(x), E[q]
//       -> Π q :^f PathOut_Z(y), E[PathOut_transport(p)[q]].
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
assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_pi_transport_func Z x y p E
    ≡ @section_pullback_func
        (@PathOut_cat Z y)
        (@PathOut_cat Z x)
        (@PathOut_transport_func Z x y p)
        E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @PathIndTgt_transport_func Z x y p E
    ≡ @pathout_pi_transport_func Z x y p E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    _
    _
    E
    (@functord_laxity_transf
      Z
      (@PathOutMotives_catd Z)
      (@Const_catd Z Cat_cat)
      (@PathOutPi_funcd Z)
      x
      y
      p)
    ≡ @PathIndTgt_transport_func Z x y p E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (s : τ (Obj (@Pi_cat (@PathOut_cat Z x) E))) ⊢
  @fapp0
    (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
    (Fibre_cat
      (@PathIndTgt_catd Z)
      (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
    (@PathIndTgt_transport_func Z x y p E)
    s
    ≡ @section_pullback_sec
        (@PathOut_cat Z y)
        (@PathOut_cat Z x)
        (@PathOut_transport_func Z x y p)
        E
        s;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (s : τ (Obj (@Pi_cat (@PathOut_cat Z x) E)))
  (q : τ (Obj (@PathOut_cat Z y))) ⊢
  @piapp0
    (@PathOut_cat Z y)
    (@pathout_motive_transport_obj Z x y p E)
    (@fapp0
      (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndTgt_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
      (@PathIndTgt_transport_func Z x y p E)
      s)
    q
    ≡ @piapp0
        (@PathOut_cat Z x)
        E
        s
        (@fapp0
          (@PathOut_cat Z y)
          (@PathOut_cat Z x)
          (@PathOut_transport_func Z x y p)
          q);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (s : τ (Obj (@Pi_cat (@PathOut_cat Z x) E))) ⊢
  @piapp0
    (@PathOut_cat Z y)
    (@pathout_motive_transport_obj Z x y p E)
    (@fapp0
      (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndTgt_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
      (@PathIndTgt_transport_func Z x y p E)
      s)
    (@pathout_refl_obj Z y)
    ≡ @piapp0
        (@PathOut_cat Z x)
        E
        s
        (@pathout_obj Z x y p);

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
assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat E k ≡ @fapp0 K Cat_cat E k;

assert [K : Cat] (A : Cat) (k : τ (Obj K)) ⊢
  Fibre_cat (Const_catd K A) k ≡ A;

assert [K : Cat] (k : τ (Obj K)) ⊢
  Fibre_cat (Terminal_catd K) k ≡ Terminal_cat;

assert [K : Cat] ⊢
  Terminal_catd K ≡ Const_catd K Terminal_cat;

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat (Op_catd E) k ≡ Op_cat (Fibre_cat E k);

assert [K : Cat] (A : Cat) ⊢
  Op_catd (Const_catd K A) ≡ Const_catd K (Op_cat A);

assert [A B : Cat] (E : τ (Catd B)) (F : τ (Functor A B)) (a : τ (Obj A)) ⊢
  Fibre_cat (Pullback_catd E F) a ≡ Fibre_cat E (fapp0 F a);

/*
  Internalized Catd/Pi over varying bases.

  Surface/formula:
    Catd_cat_func[K] = Catd(K)
    Catd_cat_func[F] = F^*
    Pi_int_funcd[K] = Pi_func(K)
    Pi_pullback_funcd(G)[x] = Pi_func(G[x]).
*/
assert [K : Cat] ⊢
  @fapp0 (Op_cat Cat_cat) Cat_cat Catd_cat_func K
    ≡ Catd_cat K;

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @fapp1_fapp0
    (Op_cat Cat_cat)
    Cat_cat
    Catd_cat_func
    B
    A
    F
    ≡ @Pullback_catd_func A B F;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B)) ⊢
  @fapp0 (@Catd_cat B) (@Catd_cat A) (@Pullback_catd_func A B F) E
    ≡ @Pullback_catd A B E F;

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat))) ⊢
  @fapp1_fapp0
    (@Catd_cat (Op_cat Cat_cat))
    (@Catd_cat K)
    (@Pullback_catd_func K (Op_cat Cat_cat) G)
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    Pi_int_funcd
    ≡ @Pi_pullback_funcd K G;

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat)))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    (@comp_cat_fapp0 K (Op_cat Cat_cat) Cat_cat Catd_cat_func G)
    (@Const_catd K Cat_cat)
    x
    (@Pi_pullback_funcd K G)
    ≡ @Pi_func (@fapp0 K (Op_cat Cat_cat) G x);

assert [K : Cat] (E : τ (Catd K)) ⊢
  fapp1_fapp0 (Pi_func K) id_funcd ≡ id_func;

/*
  Section-category and section-evaluation normal forms.

  Surface/formula:
    Pi(E) = Transf(1_K,E)
    Pi(const_K(A)) = K -> A
    Hom_Pi(s,t) = Transfd(s,t)
    s[k] = piapp0(s,k).
*/
assert [K : Cat] (E : τ (Catd K)) ⊢
  @Transf_cat K Cat_cat (@Terminal_catd K) E ≡ Pi_cat E;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @Functord_cat K (@Terminal_catd K) E ≡ Pi_cat E;

assert [K : Cat] (A : Cat) ⊢
  Pi_cat (Const_catd K A) ≡ Functor_cat K A;

assert [K : Cat] (E : τ (Catd K)) (s t : τ (Obj (Pi_cat E))) ⊢
  Hom_cat (Pi_cat E) s t
    ≡ @Transfd_cat K (@Const_catd K Terminal_cat) E s t;

assert [K : Cat] (A : Cat)
  (s t : τ (Obj (Pi_cat (@Const_catd K A)))) ⊢
  Hom_cat (Pi_cat (@Const_catd K A)) s t
    ≡ Transf_cat s t;

assert [K : Cat] (A : Cat)
  (F : τ (Obj (Pi_cat (Const_catd K A))))
  (k : τ (Obj K)) ⊢
  @piapp0 K (@Const_catd K A) F k
    ≡ @fapp0 K A F k;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (k : τ (Obj K)) ⊢
  @fapp0
    Terminal_cat
    (Fibre_cat E k)
    (@tapp0_fapp0 K Cat_cat (@Const_catd K Terminal_cat) E k s)
    Terminal_obj
    ≡ @piapp0 K E s k;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Pi_func K) E ≡ Pi_cat E;

// Component of the global internal Pi package at a fixed base.
assert [K : Cat] ⊢
  @tapp0_fapp0
    (Op_cat Cat_cat)
    Cat_cat
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    K
    Pi_int_funcd
    ≡ @Pi_func K;

/*
  Generic Sigma/Pi helper computations.

  Surface/formula:
    sigma_intro(E)[k](u) = (k,u)
    pi_eval(E)[k](s) = s[k]
    const_section_K,A(a)[k] = a
    Obj_func_A(a) = const_section_1,A(a).
*/
assert [K : Cat] (E : τ (Catd K))
  (k : τ (Obj K))
  (u : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0
    (Fibre_cat E k)
    (@Sigma_cat K E)
    (@tapp0_fapp0
      K
      Cat_cat
      E
      (@Const_catd K (@Sigma_cat K E))
      k
      (@sigma_intro_transf K E))
    u
    ≡ @Struct_sigma
        (Obj K)
        (λ kk : τ (Obj K), Obj (Fibre_cat E kk))
        k
        u;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (k : τ (Obj K)) ⊢
  @fapp0
    (Pi_cat E)
    (Fibre_cat E k)
    (@tapp0_fapp0
      K
      Cat_cat
      (@Const_catd K (@Pi_cat K E))
      E
      k
      (@pi_eval_transf K E))
    s
    ≡ @piapp0 K E s k;

assert [K : Cat] (A : Cat)
  (a : τ (Obj A)) ⊢
  @fapp0 A (@Pi_cat K (@Const_catd K A)) (@const_section_func K A) a
    ≡ @Const_func K A a;

assert [A : Cat] (a : τ (Obj A)) ⊢
  @Obj_func A a ≡ @Const_func Terminal_cat A a;

assert [A : Cat] (a : τ (Obj A)) ⊢
  @fapp0 A (@Pi_cat Terminal_cat (@Const_catd Terminal_cat A))
    (@const_section_func Terminal_cat A) a
    ≡ @Obj_func A a;

assert [A : Cat] (a : τ (Obj A)) (x y : τ (Obj Terminal_cat)) ⊢
  @fapp1_func Terminal_cat A (@Obj_func A a) x y
    ≡ @Obj_func (Hom_cat A a a) (@id A a);

assert [A : Cat] (a : τ (Obj A)) (x y : τ (Obj Terminal_cat))
  (f : τ (Hom Terminal_cat x y)) ⊢
  @fapp1_fapp0 Terminal_cat A (@Obj_func A a) x y f
    ≡ @id A a;

assert [K : Cat] (A : Cat)
  (a : τ (Obj A))
  (k : τ (Obj K)) ⊢
  @piapp0
    K
    (@Const_catd K A)
    (@fapp0 A (@Pi_cat K (@Const_catd K A)) (@const_section_func K A) a)
    k
    ≡ a;

/*
  Pullback of sections.

  Surface/formula:
    section_pullback(F,E)(s)[a] = s[F[a]]
    section_pullback_transf(F)[E] = section_pullback(F,E).
*/
assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Functord_cat B (@Const_catd B Terminal_cat) E))) ⊢
  @fapp0
    (@Functord_cat B (@Const_catd B Terminal_cat) E)
    (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F))
    (@section_pullback_func A B F E)
    s
    ≡ @section_pullback_sec A B F E s;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Functord_cat B (@Const_catd B Terminal_cat) E)))
  (a : τ (Obj A)) ⊢
  @piapp0
    A
    (@Pullback_catd A B E F)
    (@fapp0
      (@Functord_cat B (@Const_catd B Terminal_cat) E)
      (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F))
      (@section_pullback_func A B F E)
      s)
    a
    ≡ @piapp0 B E s (@fapp0 A B F a);

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B)) ⊢
  @tapp0_fapp0
    (@Catd_cat B)
    Cat_cat
    (@Pi_func B)
    (@comp_cat_fapp0
      (@Catd_cat B)
      (@Catd_cat A)
      Cat_cat
      (@Pi_func A)
      (@Pullback_catd_func A B F))
    E
    (@section_pullback_transf A B F)
    ≡ @section_pullback_func A B F E;

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @functord_laxity_transf
    (Op_cat Cat_cat)
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    Pi_int_funcd
    B
    A
    F
    ≡ @section_pullback_transf A B F;

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @functord_laxity_transf
    K
    (@comp_cat_fapp0 K (Op_cat Cat_cat) Cat_cat Catd_cat_func G)
    (@Const_catd K Cat_cat)
    (@Pi_pullback_funcd K G)
    x
    y
    p
    ≡ @section_pullback_transf
        (@fapp0 K (Op_cat Cat_cat) G y)
        (@fapp0 K (Op_cat Cat_cat) G x)
        (@fapp1_fapp0 K (Op_cat Cat_cat) G x y p);

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (E : τ (Catd (@fapp0 K (Op_cat Cat_cat) G x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@fapp0 K (Op_cat Cat_cat) G x))
    Cat_cat
    _
    _
    E
    (@functord_laxity_transf
      K
      (@comp_cat_fapp0 K (Op_cat Cat_cat) Cat_cat Catd_cat_func G)
      (@Const_catd K Cat_cat)
      (@Pi_pullback_funcd K G)
      x
      y
      p)
    ≡ @section_pullback_func
        (@fapp0 K (Op_cat Cat_cat) G y)
        (@fapp0 K (Op_cat Cat_cat) G x)
        (@fapp1_fapp0 K (Op_cat Cat_cat) G x y p)
        E;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @tapp0_fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_lhs_func K E D FF x y p)
    (@functord_transport_rhs_func K E D FF x y p)
    u
    (@functord_laxity_transf K E D FF x y p)
    ≡ @functord_laxity_fdapp1_cell K E D FF x y p u;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B)) ⊢
  @functord_laxity_fdapp1_cell
    (Op_cat Cat_cat)
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    Pi_int_funcd
    B
    A
    F
    E
    ≡ @section_pullback_func A B F E;

assert [K : Cat] (G : τ (Functor K (Op_cat Cat_cat)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (E : τ (Catd (@fapp0 K (Op_cat Cat_cat) G x))) ⊢
  @functord_laxity_fdapp1_cell
    K
    (@comp_cat_fapp0 K (Op_cat Cat_cat) Cat_cat Catd_cat_func G)
    (@Const_catd K Cat_cat)
    (@Pi_pullback_funcd K G)
    x
    y
    p
    E
    ≡ @section_pullback_func
        (@fapp0 K (Op_cat Cat_cat) G y)
        (@fapp0 K (Op_cat Cat_cat) G x)
        (@fapp1_fapp0 K (Op_cat Cat_cat) G x y p)
        E;

/*
  Sigma total category and projection-pullback normal forms.

  Surface/formula:
    Sigma_func(K)[E] = Sigma(E)
    Sigma_map(eta)(k,u) = (k, eta[k](u))
    Sigma_proj1(E)(k,u) = k
    (Sigma_proj1(R))^*D[(k,r)] = D[k]
    Pi_{(k,r):Sigma(R)} D[k] = Functord(R,D).
*/
assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Sigma_func K) E ≡ Sigma_cat E;

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D)) ⊢
  @fapp1_fapp0 (Catd_cat K) Cat_cat (@Sigma_func K) E D η
    ≡ @sigma_map_func K E D η;

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ≡ k;

assert [K : Cat] (R D : τ (Catd K)) ⊢
  @Pullback_catd (@Sigma_cat K R) K D (@Sigma_proj1_func K R)
    ≡ @Sigma_proj1_pullback_catd K R D;

assert [K : Cat] (R D : τ (Catd K))
  (k : τ (Obj K))
  (r : τ (Obj (Fibre_cat R k))) ⊢
  Fibre_cat (@Sigma_proj1_pullback_catd K R D) (Struct_sigma k r)
    ≡ Fibre_cat D k;

assert [K : Cat] (R D : τ (Catd K)) ⊢
  @Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D)
    ≡ @Functord_cat K R D;

assert [K : Cat] (R D : τ (Catd K))
  (s t : τ (Obj (@Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D)))) ⊢
  Hom_cat (@Pi_cat (@Sigma_cat K R) (@Sigma_proj1_pullback_catd K R D)) s t
    ≡ @Transfd_cat K R D s t;

assert [K A : Cat] ⊢
  @Sigma_cat K (@Const_catd K A) ≡ Product_cat K A;

assert [K A : Cat]
  (x y : τ (Obj K))
  (u v : τ (Obj A)) ⊢
  @Hom_cat
    (@Sigma_cat K (@Const_catd K A))
    (Struct_sigma x u)
    (Struct_sigma y v)
    ≡ @Product_cat
        (Hom_cat K x y)
        (Hom_cat A u v);

assert [K A : Cat]
  (x y : τ (Obj K))
  (u v : τ (Obj A))
  (p : τ (Hom K x y))
  (alpha : τ (Hom A u v)) ⊢
  @sigma_arrow K (@Const_catd K A) x y u v p alpha
    ≡ @Struct_sigma
        (Obj (Hom_cat K x y))
        (λ _ : τ (Obj (Hom_cat K x y)), Obj (Hom_cat A u v))
        p
        alpha;

/*
  Mixed-variance family constructors.

  Surface/formula:
    Functor_catd(A,B)[k] = A[k^-] -> B[k]
    Hom_catd(E,X,Y)[k] = Hom_{E[k]}(X[k^-],Y[k])
    Transf_catd(A,B,FF,GG)[k] = FF[k^-] => GG[k]
    Hom_catd(const Cat, X, Y) = Functor_catd(Op_func(X),Y).
*/
assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat (Functor_catd A B) k
    ≡ Functor_cat (Fibre_cat A k) (Fibre_cat B k);

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) (Catd_cat K)
    (@fapp0
      (Op_cat (Catd_cat (Op_cat K)))
      (Functor_cat (Catd_cat K) (Catd_cat K))
      (@Functor_catd_func K)
      A)
    B
    ≡ Functor_catd A B;

assert [K : Cat] (E : τ (Catd K))
  (X : τ (Obj (Pi_cat (Op_catd E))))
  (Y : τ (Obj (Pi_cat E)))
  (k : τ (Obj K)) ⊢
  Fibre_cat (Hom_catd E X Y) k
    ≡ Hom_cat
        (Fibre_cat E k)
        (@piapp0 K (@Op_catd K E) X k)
        (@piapp0 K E Y k);

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K))
  (FF : τ (Obj (Pi_cat (Op_catd (Functor_catd A B)))))
  (GG : τ (Obj (Pi_cat (Functor_catd A B))))
  (k : τ (Obj K)) ⊢
  Fibre_cat (Transf_catd A B FF GG) k
    ≡ Transf_cat
        (@piapp0 K (@Op_catd K (@Functor_catd K A B)) FF k)
        (@piapp0 K (@Functor_catd K A B) GG k);

assert [K : Cat]
  (X : τ (Obj (Pi_cat (Op_catd (Const_catd K Cat_cat)))))
  (Y : τ (Obj (Pi_cat (Const_catd K Cat_cat)))) ⊢
  Hom_catd (Const_catd K Cat_cat) X Y
    ≡ Functor_catd (@Op_func K (Op_cat Cat_cat) X) Y;

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K))
  (FF : τ (Obj (Pi_cat (Op_catd (Functor_catd A B)))))
  (GG : τ (Obj (Pi_cat (Functor_catd A B)))) ⊢
  Hom_catd (Functor_catd A B) FF GG
    ≡ Transf_catd A B FF GG;

/*
  PathOut category and moving-motive transport.

  Surface/formula:
    Rep_Z(x)[y] = Hom_Z(x,y)
    PathOut_Z(x) = Sigma y :^f Z, Hom_Z(x,y)
    PathOutMotives_Z[x] = Catd(PathOut_Z(x))
    PathOut_Z(p) = precomposition/pullback along p
    pathout_motive_transport(p,E) = PathOut_Z(p)^*E.
*/
assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  Fibre_cat (@Rep_catd Z x) y
    ≡ Hom_cat Z x y;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @PathOut_cat Z x
    ≡ @Sigma_cat Z (@Rep_catd Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0 (Op_cat Z) Cat_cat (@PathOut_cat_func Z) x
    ≡ @PathOut_cat Z x;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  Fibre_cat (@PathOutMotives_catd Z) x
    ≡ @Catd_cat (@PathOut_cat Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@pathout_refl_eval_func Z x)
    (@Rep_catd (@PathOut_cat Z x) (@pathout_refl_obj Z x))
    ≡ @Fibre_cat
        (@PathOut_cat Z x)
        (@Rep_catd (@PathOut_cat Z x) (@pathout_refl_obj Z x))
        (@pathout_refl_obj Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    x
    (@PathOutReflEval_funcd Z)
    ≡ @pathout_refl_eval_func Z x;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat
    (@fapp0
      (@Catd_cat (@PathOut_cat Z x))
      (@Catd_cat (@PathOut_cat Z y))
      (@fapp1_fapp0
        Z
        Cat_cat
        (@PathOutMotives_catd Z)
        x
        y
        p)
      E)
    (@pathout_refl_obj Z y)
    ≡ Fibre_cat E (@pathout_obj Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_motive_transport_obj Z x y p E
    ≡ @fapp0
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

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @PathOut_transport_func Z x y p
    ≡ @fapp1_fapp0
        (Op_cat Z)
        Cat_cat
        (@PathOut_cat_func Z)
        y
        x
        p;

assert [Z : Cat] (x y z : τ (Obj Z)) (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp0
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    (@pathout_obj Z y z q)
    ≡ @pathout_obj Z x z (@comp_fapp0 Z x y z q p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_motive_transport_obj Z x y p E
    ≡ @Pullback_catd
        (@PathOut_cat Z y)
        (@PathOut_cat Z x)
        E
        (@PathOut_transport_func Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_motive_transport_arrow Z x y p E
    ≡ @sigma_transport_arrow
        Z
        (@PathOutMotives_catd Z)
        x
        y
        p
        E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @fapp0
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    (@pathout_refl_obj Z y)
    ≡ @pathout_obj Z x y p;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @fapp0
    (Fibre_cat (@Rep_catd Z x) x)
    (Fibre_cat (@Rep_catd Z x) y)
    (@catd_transport_func Z (@Rep_catd Z x) x y p)
    (@id Z x)
    ≡ p;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @pathout_refl_arrow Z x y p
    ≡ @sigma_transport_arrow
        Z
        (@Rep_catd Z x)
        x
        y
        p
        (@id Z x);

assert [Z : Cat] (x y z : τ (Obj Z)) (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @fapp1_fapp0
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    (@pathout_refl_obj Z y)
    (@pathout_obj Z y z q)
    (@pathout_refl_arrow Z y z q)
    ≡ @sigma_map_transport_arrow
        Z
        (@Rep_catd Z y)
        (@Rep_catd Z x)
        (@fapp1_fapp0
          (Op_cat Z)
          (@Catd_cat Z)
          (@Rep_catd_func Z)
          y
          x
          p)
        y
        z
        q
        (@id Z y);

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y))
  (q : τ (Hom Z y z)) ⊢
  @comp_fapp0
    (@PathOut_cat Z x)
    (@pathout_refl_obj Z x)
    (@pathout_obj Z x y p)
    (@pathout_obj Z x z (@comp_fapp0 Z x y z q p))
    (@fapp1_fapp0
      (@PathOut_cat Z y)
      (@PathOut_cat Z x)
      (@PathOut_transport_func Z x y p)
      (@pathout_refl_obj Z y)
      (@pathout_obj Z y z q)
      (@pathout_refl_arrow Z y z q))
    (@pathout_refl_arrow Z x y p)
    ≡ @pathout_refl_arrow
        Z
        x
        z
        (@comp_fapp0 Z x y z q p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @pathout_refl_eval_base_func Z x y p E
    ≡ @fapp1_fapp0
        (@PathOut_cat Z x)
        Cat_cat
        E
        (@pathout_refl_obj Z x)
        (@pathout_obj Z x y p)
        (@pathout_refl_arrow Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Fibre_cat E (@pathout_obj Z x y p))
    (@pathout_refl_eval_base_func Z x y p E)
    u
    ≡ @fapp0
        (Hom_cat
          (@PathOut_cat Z x)
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p))
        (Fibre_cat E (@pathout_obj Z x y p))
        (@fib_cov_tapp0_func
          (@PathOut_cat Z x)
          E
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p)
          u)
        (@pathout_refl_arrow Z x y p);

/*
  Internalized path-induction source/target fibres.

  Surface/formula:
    PathOutPi_Z[x][E] = Pi(PathOut_Z(x),E)
    PathIndTgt_Z[(x,E)] = Pi(PathOut_Z(x),E)
    PathIndSrc_Z[(x,E)] = E[(x,id_x)]
    PathIndSrc_transport(p,E)(u) = E[rho_{x,y,p}](u).
*/
assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    x
    (@PathOutPi_funcd Z)
    ≡ @Pi_func (@PathOut_cat Z x);

assert [Z : Cat] ⊢
  @PathOutPi_funcd Z
    ≡ @Pi_pullback_funcd
        Z
        (@Op_func (Op_cat Z) Cat_cat (@PathOut_cat_func Z));

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E)
    ≡ @Pi_cat (@PathOut_cat Z x) E;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat (@PathIndSrc_catd Z) (Struct_sigma x E)
    ≡ Fibre_cat E (@pathout_refl_obj Z x);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  Fibre_cat
    (@PathIndSrc_catd Z)
    (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))
    ≡ Fibre_cat E (@pathout_obj Z x y p);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @PathIndSrc_transport_func Z x y p E
    ≡ @pathout_refl_eval_base_func Z x y p E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat (@PathIndSrc_catd Z) (Struct_sigma x E))
    (Fibre_cat
      (@PathIndSrc_catd Z)
      (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
    (@PathIndSrc_transport_func Z x y p E)
    u
    ≡ @fapp0
        (Hom_cat
          (@PathOut_cat Z x)
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p))
        (Fibre_cat E (@pathout_obj Z x y p))
        (@fib_cov_tapp0_func
          (@PathOut_cat Z x)
          E
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p)
          u)
        (@pathout_refl_arrow Z x y p);

/*
  Object-level PathOut notation.

  Surface/formula:
    pathout_obj(x;y,p) = (y,p)
    pathout_refl_obj(x) = (x,id_x)
    Sigma_proj1(pathout_obj(x;y,p)) = y
    pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
*/
assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @pathout_obj Z x y p
    ≡ @Struct_sigma
        (Obj Z)
        (λ yy : τ (Obj Z), Obj (Fibre_cat (@Rep_catd Z x) yy))
        y
        p;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @pathout_refl_obj Z x
    ≡ @Struct_sigma
        (Obj Z)
        (λ yy : τ (Obj Z), Obj (Fibre_cat (@Rep_catd Z x) yy))
        x
        (@id Z x);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  fapp0 (@Sigma_proj1_func Z (@Rep_catd Z x)) (@pathout_obj Z x y p)
    ≡ y;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @piapp0
    (@PathOut_cat Z x)
    (@Rep_catd (@PathOut_cat Z x) (@pathout_refl_obj Z x))
    (@pathout_refl_arrow_sec Z x)
    (@pathout_obj Z x y p)
    ≡ @pathout_refl_arrow Z x y p;

assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @Pi_cat (@PathOut_cat Z x) (@Sigma_proj1_pullback_catd Z (@Rep_catd Z x) D)
    ≡ @Functord_cat Z (@Rep_catd Z x) D;

/*
  Evaluation functors act on transformations by component evaluation.

  Surface/formula:
    fapp0_func(x)[eta] = eta[x]
    pathout_refl_eval_func(x)[eta] = eta[(x,id_x)].
*/
assert [A B : Cat] (x : τ (Obj A)) (F G : τ (Functor A B))
  (η : τ (Transf F G)) ⊢
  @fapp1_fapp0
    (@Functor_cat A B)
    B
    (@fapp0_func A B x)
    F
    G
    η
    ≡ @tapp0_fapp0 A B F G x η;

assert [Z : Cat] (x : τ (Obj Z))
  (E D : τ (Catd (@PathOut_cat Z x)))
  (η : τ (Functord E D)) ⊢
  @fapp1_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@pathout_refl_eval_func Z x)
    E
    D
    η
    ≡ @tapp0_fapp0
        (@PathOut_cat Z x)
        Cat_cat
        E
        D
        (@pathout_refl_obj Z x)
        η;

/*
  Covariant fibre transport package.

  Surface/formula:
    FibCov_target(D)[x] = Functord(Rep_Z(x),D)
    fib_cov_int(D)[x](u)[y][f] = D[f](u)
    path_ind_sec(E,u)[(y,p)] = E[rho_{x,y,p}](u).
*/
assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  Fibre_cat (@FibCov_target_catd Z D) x
    ≡ @Functord_cat Z (@Rep_catd Z x) D;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @piapp0
    (@PathOut_cat Z x)
    E
    (@path_ind_sec Z x E u)
    (@pathout_obj Z x y p)
    ≡ @fapp0
        (Hom_cat (@PathOut_cat Z x)
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p))
        (Fibre_cat E (@pathout_obj Z x y p))
        (@fib_cov_tapp0_func
          (@PathOut_cat Z x)
          E
          (@pathout_refl_obj Z x)
          (@pathout_obj Z x y p)
          u)
        (@pathout_refl_arrow Z x y p);

/*
  Edge, hom-presheaf, and dependent-hom target classifiers.

  Surface/formula:
    Edge_Z(x)[y] = Hom_Z(x,y)^op
    HomPresheaf_Z(x)[y] = Hom_Z(x,y)^op -> Cat
    HomdTargetSection_E[x] = E[y^-] -> HomPresheaf_Z(x)[y]
    HomdTarget_E[x] = Pi_y HomdTargetSection_E[x][y].
*/
assert [Z : Cat] (x : τ (Obj (Op_cat Z))) (y : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat
    (@fapp0 (Op_cat Z) (Catd_cat Z) (@Edge_catd_func Z) x)
    y
    ≡ Op_cat (Hom_cat Z x y);

assert [Z : Cat] (x : τ (Obj Z)) (y : τ (Obj (Op_cat Z))) ⊢
  Fibre_cat (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x) y
    ≡ Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat;

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @Homd_target_section_catd Z E x
    ≡ @Functor_catd
        (Op_cat Z)
        E
        (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x);

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_catd Z E) x
    ≡ Pi_cat
        (Functor_catd
          E
          (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x));

/*
  Internal covariant transport components.

  Surface/formula:
    FibCov_target(E)[x] = Functord(hom_K(x,-),E)
    fib_cov_src(x)(u) = fib_cov_transf(x,u)
    fib_cov_transf(x,u)[y] = fib_cov_tapp0_func(x,y,u).
*/
assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  Fibre_cat (@FibCov_target_catd K E) x
    ≡ @Functord_cat K (@hom_ K K (@id_func K) x) E;

assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  Obj (Fibre_cat (@FibCov_target_catd K E) x)
    ≡ @Functord K (@hom_ K K (@id_func K) x) E;

assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  @Transf_cat K Cat_cat (@hom_ K K (@id_func K) x) E
    ≡ @Functord_cat K (@hom_ K K (@id_func K) x) E;

assert [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    E
    (@FibCov_target_catd K E)
    x
    (@fib_cov_int K E)
    ≡ @fib_cov_src_func K E x;

assert [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@fib_cov_src_func K E x) u
    ≡ @fib_cov_transf K E x u;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    (@hom_ K K (@id_func K) x)
    E
    y
    (@fib_cov_transf K E x u)
    ≡ @fib_cov_tapp0_func K E x y u;

/*
  Displayed functor calculus.

  Surface/formula:
    Op_funcd(id_E) = id_{E^op}
    Op_funcd(Op_funcd(FF)) = FF
    (FF o id_E) = FF
    (id_D o GG) = GG
    Fibre_func(FF,z) = FF[z].
*/
assert [K : Cat] (E : τ (Catd K)) ⊢
  @Op_funcd K E E (@id_funcd K E)
    ≡ @id_funcd K (@Op_catd K E);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @Op_funcd K (@Op_catd K E) (@Op_catd K D) (@Op_funcd K E D FF)
    ≡ FF;

assert [K : Cat] (E D C : τ (Catd K))
  (FF : τ (Functord D C))
  (GG : τ (Functord E D)) ⊢
  @comp_fapp0 (@Catd_cat K) E D C FF GG
    ≡ @comp_catd_fapp0 K E D C FF GG;

assert [K : Cat] (E C : τ (Catd K))
  (FF : τ (Functord E C)) ⊢
  @comp_catd_fapp0 K E E C FF (@id_funcd K E)
    ≡ FF;

assert [K : Cat] (E D : τ (Catd K))
  (GG : τ (Functord E D)) ⊢
  @comp_catd_fapp0 K E D D (@id_funcd K D) GG
    ≡ GG;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0
    K
    Cat_cat
    (@Op_catd K E)
    (@Op_catd K D)
    x
    (@Op_funcd K E D FF)
    ≡ @Op_func
        (Fibre_cat E x)
        (Fibre_cat D x)
        (@tapp0_fapp0 K Cat_cat E D x FF);

assert [K : Cat] (E : τ (Catd K)) (y : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat E E y (@id_funcd K E)
    ≡ @id_func (Fibre_cat E y);

/*
  Displayed transfor application packages.

  Surface/formula:
    tdapp1_int_func_transfd(FF,GG)[epsilon] = tdapp1_int_fapp0(epsilon)
    tdapp1_int_fapp0(id_FF) = fdapp1_int_transfd(FF)
    tdapp0_func(z)[epsilon] = epsilon[z]
    Fibre_transf(epsilon,z) = epsilon[z].
*/
assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (@Transfd K E D FF GG)) ⊢
  fapp0 (@tdapp1_int_func_transfd K E D FF GG) ϵ
    ≡ @tdapp1_int_fapp0_transfd K E D FF GG ϵ;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ ϵ' : τ (@Transfd K E D FF GG)) ⊢
  @fapp1_func _ _ (@tdapp1_int_func_transfd K E D FF GG) ϵ ϵ'
    ≡ @tdapp1_int_fapp1_func_transfd K E D FF GG ϵ ϵ';

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @tdapp1_int_fapp0_transfd K E D FF FF
    (@id (@Functord_cat K E D) FF)
    ≡ @fdapp1_int_transfd K E D FF;

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E))) ⊢
  @tdapp1_int_fapp0_transfd
    K
    (@Const_catd K Terminal_cat)
    E
    s
    s
    (@id_transfd K (@Const_catd K Terminal_cat) E s)
    ≡ @fdapp1_int_transfd K (@Const_catd K Terminal_cat) E s;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (z : τ (Obj K)) (ϵ : τ (@Transfd K E D FF GG)) ⊢
  fapp0 (@tdapp0_func K E D FF GG z) ϵ
    ≡ @tdapp0_fapp0 K E D FF GG z ϵ;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K)) ⊢
  @Fibre_func K E D FF z
    ≡ @tapp0_fapp0 K Cat_cat E D z FF;

assert [K : Cat] (E : τ (Catd K)) (z : τ (Obj K)) ⊢
  @Fibre_func K E E (@id_funcd K E) z
    ≡ @id_func (Fibre_cat E z);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K)) ⊢
  @Fibre_func
    K
    (@Op_catd K E)
    (@Op_catd K D)
    (@Op_funcd K E D FF)
    z
    ≡ @Op_func
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (z : τ (Obj K))
  (u : τ (Obj (Fibre_cat (@Op_catd K E) z))) ⊢
  @fapp0
    (Fibre_cat (@Op_catd K E) z)
    (Fibre_cat (@Op_catd K D) z)
    (@Fibre_func K (@Op_catd K E) (@Op_catd K D) (@Op_funcd K E D FF) z)
    u
    ≡ @fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z)
        u;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (@Transfd K E D FF GG)) (z : τ (Obj K)) ⊢
  @Fibre_transf K E D FF GG ϵ z
    ≡ @tdapp0_fapp0 K E D FF GG z ϵ;

assert [K : Cat] (E D : τ (Catd K)) (FF GG : τ (Functord E D))
  (ϵ : τ (@Transfd K E D FF GG))
  (z : τ (Obj K))
  (u : τ (Obj (Fibre_cat E z))) ⊢
  @Fibre_transf_app K E D FF GG ϵ z u
    ≡ @tapp0_fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@Fibre_func K E D FF z)
        (@Fibre_func K E D GG z)
        u
        (@Fibre_transf K E D FF GG ϵ z);

/*
  Generic displayed transport routes.

  Surface/formula:
    catd_transport(E,p) = E[p]
    functord_transport(FF,p) = FF[p]
    functord_transport_lhs(FF,p)(u) = D[p](FF[x](u))
    functord_transport_rhs(FF,p)(u) = FF[y](E[p](u))
    Sigma_catd_transport(FF,p,r) = Sigma(FF)[sigma_transport(p,r)].
*/
assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @catd_transport_func K E x y p
    ≡ @fapp1_fapp0 K Cat_cat E x y p;

assert [K : Cat] (E : τ (Catd K))
  (x y z : τ (Obj K))
  (p : τ (Hom K x y))
  (q : τ (Hom K y z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E y)
    (Fibre_cat E z)
    (@catd_transport_func K E y z q)
    (@fapp0
      (Fibre_cat E x)
      (Fibre_cat E y)
      (@catd_transport_func K E x y p)
      u)
    ≡ @fapp0
        (Fibre_cat E x)
        (Fibre_cat E z)
        (@catd_transport_func K E x z (@comp_fapp0 K x y z q p))
        u;

assert [K : Cat] (E : τ (Catd K))
  (x y z : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (w : τ (Obj (Fibre_cat E z)))
  (p : τ (Hom K x y))
  (q : τ (Hom K y z))
  (alpha : τ (Hom
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u)
      v))
  (beta : τ (Hom
      (Fibre_cat E z)
      (@fapp0
        (Fibre_cat E y)
        (Fibre_cat E z)
        (@catd_transport_func K E y z q)
        v)
      w)) ⊢
  @comp_fapp0
    (@Sigma_cat K E)
    (Struct_sigma x u)
    (Struct_sigma y v)
    (Struct_sigma z w)
    (@sigma_arrow K E y z v w q beta)
    (@sigma_arrow K E x y u v p alpha)
    ≡ @sigma_arrow
        K
        E
        x
        z
        u
        w
        (@comp_fapp0 K x y z q p)
        (@comp_fapp0
          (Fibre_cat E z)
          (@fapp0
            (Fibre_cat E x)
            (Fibre_cat E z)
            (@catd_transport_func K E x z (@comp_fapp0 K x y z q p))
            u)
          (@fapp0
            (Fibre_cat E y)
            (Fibre_cat E z)
            (@catd_transport_func K E y z q)
            v)
          w
          beta
          (@fapp1_fapp0
            (Fibre_cat E y)
            (Fibre_cat E z)
            (@catd_transport_func K E y z q)
            (@fapp0
              (Fibre_cat E x)
              (Fibre_cat E y)
              (@catd_transport_func K E x y p)
              u)
            v
            alpha));

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y)) ⊢
  @functord_transport_func K E D FF x y p
    ≡ @tapp1_fapp0 K Cat_cat E D x y FF p;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_lhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat D x)
        (Fibre_cat D y)
        (@catd_transport_func K D x y p)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@Fibre_func K E D FF x)
          u);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_rhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat E y)
        (Fibre_cat D y)
        (@Fibre_func K E D FF y)
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat E y)
          (@catd_transport_func K E x y p)
          u);

// Object-level strict naturality of displayed functor transport: both named
// coherence routes compute to the internal off-diagonal component.
assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_lhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_func K E D FF x y p)
        u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @fapp0
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_rhs_func K E D FF x y p)
    u
    ≡ @fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_func K E D FF x y p)
        u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @sigma_map_transport_fibre_arrow K E D FF x y p u
    ≡ sigma_Snd (@sigma_map_transport_arrow K E D FF x y p u);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @sigma_map_transport_fibre_arrow K E D FF x y p u
    ≡ @fapp1_fapp0
        (Fibre_cat E y)
        (Fibre_cat D y)
        (@tapp0_fapp0 K Cat_cat E D y FF)
        (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u)
        (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u)
        (@homd_id_canonical_triangle K E x y p u);

assert [K : Cat] (R : τ (Catd K))
  (FF : τ (Functord R (@Const_catd K Cat_cat)))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (r : τ (Obj (Fibre_cat R x))) ⊢
  @fapp1_fapp0
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
    (@sigma_transport_arrow K R x y p r)
    ≡ @Sigma_catd_transport_func K R FF x y p r;

/*
  Internal dependent-hom constructor projections.

  Surface/formula:
    homd_int(FF)[x](u) = homd_src_sec(FF,x,u)
    homd_src_sec(FF,x,u)[y] = homd_tgt_func(FF,x,u,y)
    homd_tgt_func(FF,x,u,y)(v) = homd_(FF,x,u,y,v).
*/
assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Op_catd Z E)
    (@Homd_target_catd Z D)
    x
    (@homd_int Z D E FF)
    ≡ @homd_src_func Z D E FF x;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @Fibre_func
    Z
    (@Op_catd Z E)
    (@Homd_target_catd Z D)
    (@homd_int Z D E FF)
    x
    ≡ @homd_src_func Z D E FF x;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat (@Op_catd Z E) x))) ⊢
  @fapp0
    (Fibre_cat (@Op_catd Z E) x)
    (Fibre_cat (@Homd_target_catd Z D) x)
    (@Fibre_func Z (@Op_catd Z E) (@Homd_target_catd Z D) (@homd_int Z D E FF) x)
    u
    ≡ @homd_src_sec Z D E FF x u;

// Regression for the `homd_int` first projection. The rule itself keeps the
// source/target family arguments implicit; this assertion may spell them out
// because it is not a rewrite-pattern LHS.
assert [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Op_catd Z E)
    (@Homd_target_catd Z E)
    x
    (@homd_int Z E E (@id_funcd Z E))
    ≡ @homd_src_func Z E E (@id_funcd Z E) x;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  fapp0 (@tdapp1_int_func_transfd K E D FF FF)
    (@id (@Functord_cat K E D) FF)
    ≡ @fdapp1_int_transfd K E D FF;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_src_func Z D E FF x) u
    ≡ @homd_src_sec Z D E FF x u;

assert [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_src_func Z E E (@id_funcd Z E) x) u
    ≡ @homd_src_sec Z E E (@id_funcd Z E) x u;

/*
  Terminal-source specializations of the dependent-hom source projection.

  Surface/formula:
    homd_src_func(1,1,id)[x] = constant terminal section
    Fibre_func(homd_int(id_1),x) = that same terminal section.
*/
assert [K : Cat] (x : τ (Obj K)) ⊢
  @homd_src_func K
    (@Const_catd K Terminal_cat)
    (@Const_catd K Terminal_cat)
    (@id_funcd K (@Const_catd K Terminal_cat))
    x
    ≡ @Obj_func
        (Pi_cat (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x))
        (@homd_src_sec K
          (@Const_catd K Terminal_cat)
          (@Const_catd K Terminal_cat)
          (@id_funcd K (@Const_catd K Terminal_cat))
          x
          Terminal_obj);

assert [K : Cat] (x : τ (Obj K)) ⊢
  @Fibre_func
    K
    (@Op_catd K (@Const_catd K Terminal_cat))
    (@Homd_target_catd K (@Const_catd K Terminal_cat))
    (@homd_int
      K
      (@Const_catd K Terminal_cat)
      (@Const_catd K Terminal_cat)
      (@id_funcd K (@Const_catd K Terminal_cat)))
    x
    ≡ @Obj_func
        (Pi_cat (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x))
        (@homd_src_sec K
          (@Const_catd K Terminal_cat)
          (@Const_catd K Terminal_cat)
          (@id_funcd K (@Const_catd K Terminal_cat))
          x
          Terminal_obj);

/*
  Dependent-hom target projection and element computation.

  Surface/formula:
    homd_src_sec(FF,x,u)[y] = homd_tgt_func(FF,x,u,y)
    homd_tgt_func(FF,x,u,y)(v) = homd_(FF,x,u,y,v)
    with the terminal-source case reducing to the displayed Pi-app source.
*/
assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat Z)
    (@Functor_catd
      (Op_cat Z)
      D
      (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x))
    (@homd_src_sec Z D E FF x u)
    y
    ≡ @homd_tgt_func Z D E FF x u y;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat Z)
    (@Functor_catd
      (Op_cat Z)
      E
      (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x))
    (@homd_src_sec Z E E (@id_funcd Z E) x u)
    y
    ≡ @homd_tgt_func Z E E (@id_funcd Z E) x u y;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  fapp0 (@homd_tgt_func Z E E (@id_funcd Z E) x u y) v
    ≡ @homd_ Z E E (@id_funcd Z E) x u y v;

assert [K : Cat] (x y : τ (Obj K)) ⊢
  @homd_tgt_func K
    (@Const_catd K Terminal_cat)
    (@Const_catd K Terminal_cat)
    (@id_funcd K (@Const_catd K Terminal_cat))
    x
    Terminal_obj
    y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd_func K) x)
          y)
        (@Terminal_catd (Op_cat (Hom_cat K x y)));

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @homd_tgt_func K (@Const_catd K Terminal_cat) E s x u y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd_func K) x)
          y)
        (@homd_
          K
          E
          E
          (@id_funcd K E)
          x
          u
          y
          (@piapp0 K E s y));

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat K)
    (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x)
    (@homd_src_sec K (@Const_catd K Terminal_cat) E s x u)
    y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd_func K) x)
          y)
        (@homd_
          K
          E
          E
          (@id_funcd K E)
          x
          u
          y
          (@piapp0 K E s y));

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_tgt_func K (@Const_catd K Terminal_cat) E s x u y) Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        u
        y
        (@piapp0 K E s y);

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K)) ⊢
  fapp0
    (@piapp0
      (Op_cat K)
      (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x)
      (@homd_src_sec
        K
        (@Const_catd K Terminal_cat)
        E
        s
        x
        (@piapp0 K E s x))
      y)
    Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        (@piapp0 K E s x)
        y
        (@piapp0 K E s y);

assert [K : Cat] (x y : τ (Obj K)) ⊢
  fapp0
    (@homd_tgt_func K
      (@Const_catd K Terminal_cat)
      (@Const_catd K Terminal_cat)
      (@id_funcd K (@Const_catd K Terminal_cat))
      x
      Terminal_obj
      y)
    Terminal_obj
    ≡ @Terminal_catd (Op_cat (Hom_cat K x y));

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  fapp0 (@homd_tgt_func Z D E FF x u y) v
    ≡ @homd_ Z D E FF x u y v;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  @homd_ Z D E FF x u y v
    ≡ @hom_con
        (Fibre_cat E y)
        (@fapp0
          (Fibre_cat D y)
          (Fibre_cat E y)
          (@tapp0_fapp0 Z Cat_cat D E y FF)
        v)
        (Hom_cat Z x y)
        (@fib_cov_tapp0_func Z E x y u);

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @homd_ Z E E (@id_funcd Z E) x u y v
    ≡ @hom_con
        (Fibre_cat E y)
        v
        (Hom_cat Z x y)
        (@fib_cov_tapp0_func Z E x y u);

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0
    (@functord_laxity_fdapp1_hom_func K E D FF x y p u _)
    (@homd_id_canonical_triangle K E x y p u)
    ≡ @functord_laxity_fdapp1_cell K E D FF x y p u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0
    (@functord_laxity_fdapp1_hom_func
      K E D FF x y p u
      (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
    (@id
      (@fapp0 K Cat_cat E y)
      (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
    ≡ @functord_laxity_fdapp1_cell K E D FF x y p u;

/*
  End-to-end displayed internal-hom extraction checks.

  The third projection assertion below uses explicit canonical source/target
  slots for `tapp0_fapp0`. The readable form

    tapp0_fapp0 v (functord_laxity_fdapp1_tgt_arrow ...)

  is mathematically correct but asks Lambdapi to reconstruct too many implicit
  projection parameters and can time out. The `tgt_arrow` head itself is typed
  in reduced `Transf` form; the explicit assertion below is still the robust
  regression surface.
*/
assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @Fibre_transf_app
    K
    (@Op_catd K E)
    (@Homd_target_catd K E)
    (@homd_int K E E (@id_funcd K E))
    (@comp_catd_fapp0
      K
      (@Op_catd K E)
      (@Op_catd K D)
      (@Homd_target_catd K E)
      (@homd_int K E D FF)
      (@Op_funcd K E D FF))
    (@fdapp1_int_transfd K E D FF)
    x
    u
    ≡ @functord_laxity_fdapp1_section_arrow K E D FF x u;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  tapp0_fapp0
    Terminal_obj
    (tdapp0_fapp0 y (@functord_laxity_fdapp1_section_arrow K E D FF x u))
    ≡ @functord_laxity_fdapp1_tgt_arrow K E D FF x u y;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @tapp0_fapp0
    (Fibre_cat E y)
    (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
    (@homd_id_tgt_func K E x u y)
    (@homd_ff_tgt_func K E D FF x u y)
    v
    (@functord_laxity_fdapp1_tgt_arrow K E D FF x u y)
    ≡ @functord_laxity_fdapp1_presheaf_arrow K E D FF x u y v;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  @fapp1_fapp0
    (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
    Cat_cat
    (@fapp0_func (Op_cat (Hom_cat K x y)) Cat_cat p)
    (fapp0 (@homd_id_tgt_func K E x u y) v)
    (fapp0 (@homd_ff_tgt_func K E D FF x u y) v)
    (@functord_laxity_fdapp1_presheaf_arrow K E D FF x u y v)
    ≡ @functord_laxity_fdapp1_hom_func K E D FF x y p u v;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0
    (@functord_laxity_fdapp1_hom_func K E D FF x y p u _)
    (@homd_id_canonical_triangle K E x y p u)
    ≡ @tapp0_fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y p)
        (@functord_transport_rhs_func K E D FF x y p)
        u
        (@functord_laxity_transf K E D FF x y p);

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K)) ⊢
  @homd_
    K
    (@Const_catd K Terminal_cat)
    E
    s
    x
    (@piapp0 K E s x)
    y
    Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        (@piapp0 K E s x)
        y
        (@piapp0 K E s y);

/*
  Constant and terminal dependent-hom specializations.

  Surface/formula:
    homd_(const A, const A, id; x,u,y,v) = const(Hom_A(u,v))
    homd_(1,1,id; x,u,y,v) = terminal
    and their functor/action projections reduce to the same constants.
*/
assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y))) ⊢
  @homd_ K
    (Const_catd K A)
    (Const_catd K A)
    (@id_funcd K (Const_catd K A))
    x u y v
    ≡ @Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v);

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Const_catd K A)
      (Const_catd K A)
      (@id_funcd K (Const_catd K A))
      x u y v)
    f
    g
    ≡ @fapp1_func
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v))
        f
        g;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y))))
  (alpha : τ (Hom (Op_cat (Hom_cat K x y)) f g)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Const_catd K A)
      (Const_catd K A)
      (@id_funcd K (Const_catd K A))
      x u y v)
    f
    g
    alpha
    ≡ @fapp1_fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v))
        f
        g
        alpha;

assert [K : Cat]
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Terminal_catd K) x)))
  (v : τ (Obj (Fibre_cat (Terminal_catd K) y))) ⊢
  @homd_ K
    (Terminal_catd K)
    (Terminal_catd K)
    (@id_funcd K (Terminal_catd K))
    x u y v
    ≡ @Terminal_catd (Op_cat (Hom_cat K x y));

assert [K : Cat]
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Terminal_catd K) x)))
  (v : τ (Obj (Fibre_cat (Terminal_catd K) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Terminal_catd K)
      (Terminal_catd K)
      (@id_funcd K (Terminal_catd K))
      x u y v)
    f
    g
    ≡ @fapp1_func
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Terminal_catd (Op_cat (Hom_cat K x y)))
        f
        g;

assert [K : Cat]
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Terminal_catd K) x)))
  (v : τ (Obj (Fibre_cat (Terminal_catd K) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y))))
  (alpha : τ (Hom (Op_cat (Hom_cat K x y)) f g)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K
      (Terminal_catd K)
      (Terminal_catd K)
      (@id_funcd K (Terminal_catd K))
      x u y v)
    f
    g
    alpha
    ≡ @fapp1_fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@Terminal_catd (Op_cat (Hom_cat K x y)))
        f
        g
        alpha;

/*
  Fibre transport and section application source formulas.

  Surface/formula:
    fib_cov_tapp0(const A,x,y,u) = const_{Hom_K(x,y)}(u)
    piapp1_src_obj(s,x,y,f) = E[f](s[x])
    piapp1_fapp0(s,f) = piapp1_func(s)(f).
*/
assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x))) ⊢
  @fib_cov_tapp0_func K (@Const_catd K A) x y u
    ≡ @Const_func (Hom_cat K x y) A u;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (f : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x))) ⊢
  fapp0 (@fib_cov_tapp0_func K (@Const_catd K A) x y u) f
    ≡ u;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_ K E E (@id_funcd K E) x u y v)
    f
    ≡ Hom_cat (Fibre_cat E y)
        (fapp0 (@fib_cov_tapp0_func K E x y u) f)
        v;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_src_obj K E s x y f
    ≡ fapp0 (@fib_cov_tapp0_func K E x y (@piapp0 K E s x)) f;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  fapp0
    (homd_
      (@id_funcd K E)
      x (@piapp0 K E s x)
      y (@piapp0 K E s y))
    f
    ≡ Hom_cat (Fibre_cat E y)
        (@piapp1_src_obj K E s x y f)
        (@piapp0 K E s y);

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_
      K
      (@Const_catd K Terminal_cat)
      E
      s
      x
      (@piapp0 K E s x)
      y
      Terminal_obj)
    f
    ≡ Hom_cat (Fibre_cat E y)
        (@piapp1_src_obj K E s x y f)
        (@piapp0 K E s y);

assert [K : Cat] (A : Cat)
  (s : τ (Obj (Pi_cat (Const_catd K A))))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_src_obj K (@Const_catd K A) s x y f
    ≡ @fapp0 K A s x;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K E E (@id_funcd K E) x u y v)
    f
    g
    ≡ @fapp1_func
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@hom_con
          (Fibre_cat E y)
          v
          (Hom_cat K x y)
          (@fib_cov_tapp0_func K E x y u))
        f
        g;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y))))
  (alpha : τ (Hom (Op_cat (Hom_cat K x y)) f g)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K E E (@id_funcd K E) x u y v)
    f
    g
    alpha
    ≡ @fapp1_fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@hom_con
          (Fibre_cat E y)
          v
          (Hom_cat K x y)
          (@fib_cov_tapp0_func K E x y u))
        f
        g
        alpha;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_fapp0 K E s x y f
    ≡ piapp0 (@piapp1_func K E s x y) f;

assert [K : Cat] (A : Cat)
  (s : τ (Obj (Pi_cat (Const_catd K A))))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_fapp0 K (@Const_catd K A) s x y f
    ≡ @fapp1_fapp0 K A s x y f;

/*
  Sigma homs and Sigma-map action.

  Surface/formula:
    Hom_Sigma(E)((x,u),(y,v)) = Sigma_{f : Hom_Z(x,y)^op} homd(id_E,x,u,y,v)
    Sigma_map(eta)(k,u) = (k, eta[k](u))
    Sigma_proj1 o Sigma_map(eta) = Sigma_proj1.
*/
assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  Hom_cat (@Sigma_cat Z E) (Struct_sigma x u) (Struct_sigma y v)
    ≡ Op_cat
        (@Sigma_cat
          (Op_cat (Hom_cat Z x y))
          (@homd_ Z E E (@id_funcd Z E) x u y v));

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0 (@Sigma_cat K E) (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma k u)
    ≡ @Struct_sigma
        (Obj K)
        (λ kk : τ (Obj K), Obj (Fibre_cat D kk))
        k
        (@fapp0 (Fibre_cat E k) (Fibre_cat D k)
          (@tapp0_fapp0 K Cat_cat E D k η)
          u);

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (x y : τ (Obj K))
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
      v)) ⊢
  @fapp1_fapp0
    (@Sigma_cat K E)
    (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma x u)
    (Struct_sigma y v)
    (@sigma_arrow K E x y u v p alpha)
    ≡ @sigma_arrow
        K
        D
        x
        y
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@tapp0_fapp0 K Cat_cat E D x η)
          u)
        (@fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          v)
        p
        (@fapp1_fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          (@fapp0
            (Fibre_cat E x)
            (Fibre_cat E y)
            (@catd_transport_func K E x y p)
            u)
          v
          alpha);

// A Sigma map does not preserve canonical transport strictly for arbitrary
// displayed functors. The image exposes the action on the canonical homd
// triangle; strict/cartesian preservation is a later specialization.
assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @sigma_map_transport_arrow K E D η x y p u
    ≡ @sigma_arrow
        K
        D
        x
        y
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@tapp0_fapp0 K Cat_cat E D x η)
          u)
        (@fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u))
        p
        (@fapp1_fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u)
          (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u)
          (@homd_id_canonical_triangle K E x y p u));

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D)) ⊢
  @comp_cat_fapp0 (@Sigma_cat K E) (@Sigma_cat K D) K
    (@Sigma_proj1_func K D)
    (@sigma_map_func K E D η)
    ≡ @Sigma_proj1_func K E;

/*
  Section-dependent-hom composition normal forms.

  Surface/formula:
    (homd_int(s) o Op_funcd(s))[x](*) = homd_src_sec(s,x,s[x])
    evaluating at y and * gives homd_(id_E,x,s[x],y,s[y]).
*/
assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x : τ (Obj K)) ⊢
  @fapp0
    (Fibre_cat (@Op_catd K (@Const_catd K Terminal_cat)) x)
    (Fibre_cat (@Homd_target_catd K (@Const_catd K Terminal_cat)) x)
    (@Fibre_func
      K
      (@Op_catd K (@Const_catd K Terminal_cat))
      (@Homd_target_catd K (@Const_catd K Terminal_cat))
      (@comp_catd_fapp0
        K
        (@Op_catd K (@Const_catd K Terminal_cat))
        (@Op_catd K E)
        (@Homd_target_catd K (@Const_catd K Terminal_cat))
        (@homd_int K (@Const_catd K Terminal_cat) E s)
        (@Op_funcd K (@Const_catd K Terminal_cat) E s))
      x)
    Terminal_obj
    ≡ @homd_src_sec
        K
        (@Const_catd K Terminal_cat)
        E
        s
        x
        (@piapp0 K E s x);

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K)) ⊢
  fapp0
    (@piapp0
      (Op_cat K)
      (@Homd_target_section_catd K (@Const_catd K Terminal_cat) x)
      (@fapp0
        (Fibre_cat (@Op_catd K (@Const_catd K Terminal_cat)) x)
        (Fibre_cat (@Homd_target_catd K (@Const_catd K Terminal_cat)) x)
        (@Fibre_func
          K
          (@Op_catd K (@Const_catd K Terminal_cat))
          (@Homd_target_catd K (@Const_catd K Terminal_cat))
          (@comp_catd_fapp0
            K
            (@Op_catd K (@Const_catd K Terminal_cat))
            (@Op_catd K E)
            (@Homd_target_catd K (@Const_catd K Terminal_cat))
            (@homd_int K (@Const_catd K Terminal_cat) E s)
            (@Op_funcd K (@Const_catd K Terminal_cat) E s))
          x)
        Terminal_obj)
      y)
    Terminal_obj
    ≡ @homd_
        K
        E
        E
        (@id_funcd K E)
        x
        (@piapp0 K E s x)
        y
        (@piapp0 K E s y);
