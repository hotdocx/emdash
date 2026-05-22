/*
  m- / emdash3.2
  Directed-family mixed-variance v3.2 migration draft.

  This file is forked from emdash3_1.lp and implements
  reports/REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md incrementally.  It uses
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
    - `homd_int (id_funcd E)`, after projection at x,u,y,v, normalizes through
      `homd_src_func`, `homd_src_sec`, `homd_tgt_func`, then generalized
      `homd_` at the identity displayed functor.
    - `homd_int FF`, for `FF : Functord D E`, follows the generalized
      `homd_src_funcd`, `homd_src_secd`, `homd_tgt_funcd`, then `homd_`.

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
      `HomPresheaf_catd ...`, or `Homd_target_catd ...`, or a compound
      canonical expression such as `Op_cat (Hom_cat ...)`.
    - Prefer small projection rules with stable heads over one large nested
      redex. The homd projection path is split into `tapp0_fapp0` and `fapp0`
      folds; surface `piapp0` notation unfolds through `tapp0_fapp0`.
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
      `Transfd_cat`, `Pi_cat`) are elaboration aids.  They are not semantic
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
    - `Pi_cat E`: stable section category for a directed family. It joins
      `Functord_cat (Const_catd K Terminal_cat) E`; the corresponding
      `Transf_cat` source reaches it through the canonical `Functord_cat`
      contraction.
    - `Sigma_cat E`: object decoding is Sigma-shaped; homs between total
      objects route through the endpoint `homd_`.
    - `Functor_catd` / `Functor_catd_mix_func`: mixed-variance family formation
      is functorial in family arguments, not just an object-level recipe.
    - `Edge_catd_fam` / `HomPresheaf_catd`: internal representable/presheaf-family
      classifiers.  Keep them as named constructor pipelines; do not inline
      them into rewrite-rule LHSs.
    - `Homd_*`: source/section/target family names are readability and
      assertion handles.  Projection-rule LHSs should keep those inferred
      source/target family arguments implicit.
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
    - Pointwise displayed-functor calculus: `Op_funcd` projects through
      `tapp0_fapp0` to ordinary fibre opposites. The analogous displayed
      composition projection is deferred: the semantic E/C outer-slot form
      validates when appended late but times out near the projection-rule block,
      while the D/C outer-slot form is not the intended general E[x] -> C[x]
      projection.
    - `fdapp1_int_fibre_transf` / `fdapp1_int_fibre_app`: derived projections
      of the internal displayed hom-action, still below any external
      `fdapp1_*` surface API.
    - `piapp1_func` / `piapp1_fapp0`: section action over a base arrow. The
      capped component is a definition by `piapp0`; the terminal-specialization
      fold from displayed internal action is installed near the late projection
      block.
    - `Terminal_catd K` and `piapp0` are readability definitions, not rewrite
      discriminators. Operational rules use the unfolded constant-terminal
      source or lower-level `tapp0_fapp0` folds.
    - Generic Sigma/Pi weakening helpers have basic stable beta assertions; any
      richer coherence helpers remain deferred until needed.
*/

// -------------------------------------------------------------------------------------------------
// 0. Groupoid universe and equality
// -------------------------------------------------------------------------------------------------

constant symbol Grpd : TYPE;
injective symbol τ : Grpd → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Grpd;
builtin "P" ≔ τ;

constant symbol = : Π [a: Grpd], τ a → τ a → Grpd;
notation = infix 10;

constant symbol eq_refl : Π [a: Grpd], Π x: τ a, τ (x = x);

symbol ind_eq : Π [a: Grpd], Π [x: τ a], Π [y: τ a],
  τ (x = y) → Π p: (τ a → Grpd), τ (p y) → τ (p x);
rule ind_eq (eq_refl $x) $p $u ↪ $u;

symbol eq_trans : Π [a : Grpd], Π [x : τ a], Π [y : τ a], Π [z : τ a],
  τ (x = y) → τ (y = z) → τ (x = z)
≔ λ a x y z p q, ind_eq p (λ t : τ a, t = z) q;

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

inductive unit : TYPE ≔ | tt : unit;

constant symbol Unit_grpd : Grpd;
rule τ Unit_grpd ↪ unit;

inductive nat : TYPE ≔
| zero : nat
| succ : nat → nat;

// -------------------------------------------------------------------------------------------------
// 1. Core categories
// -------------------------------------------------------------------------------------------------

constant symbol Cat : TYPE;

symbol Obj : Cat → Grpd;

injective symbol Hom_cat : Π (A : Cat) (X_A Y_A : τ (Obj A)), Cat;

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

injective symbol Op_cat : Cat → Cat;
rule Op_cat (Op_cat $A) ↪ $A;
rule Obj (Op_cat $A) ↪ Obj $A;
rule Hom_cat (Op_cat $A) $X $Y ↪ Hom_cat $A $Y $X;
rule @id (Op_cat $A) $X ↪ @id $A $X;
rule @comp_fapp0 (Op_cat $A) $X $Y $Z $g $f ↪ @comp_fapp0 $A $Z $Y $X $f $g;

// Path categories internalize HoTT equality as a groupoidal category.
injective symbol Path_cat : Grpd → Cat;
rule Obj (Path_cat $A) ↪ $A;
rule Hom_cat (Path_cat $A) $x $y ↪ Path_cat ($x = $y);
rule @id (Path_cat $A) $x ↪ eq_refl $x;
rule @comp_fapp0 (Path_cat $A) $x $y $z $q $p ↪ eq_trans $p $q;
rule Op_cat (Path_cat $A) ↪ Path_cat $A;

symbol Core_cat (C : Cat) : Cat ≔ Path_cat (Obj C);

assert [A : Grpd] ⊢ Obj (Path_cat A) ≡ A;
assert [A : Grpd] (x y : τ A) ⊢ Hom_cat (Path_cat A) x y ≡ Path_cat (x = y);
assert [A : Grpd] (x : τ A) ⊢ @id (Path_cat A) x ≡ eq_refl x;
assert [A : Grpd] (x y z : τ A) (p : τ (x = y)) (q : τ (y = z)) ⊢
  @comp_fapp0 (Path_cat A) x y z q p ≡ eq_trans p q;

// -------------------------------------------------------------------------------------------------
// 2. Ordinary functors and universe categories
// -------------------------------------------------------------------------------------------------

injective symbol Functor_cat : Π (A B : Cat), Cat;

injective symbol Functor (A B : Cat) : Grpd
≔ Obj (Functor_cat A B);

unif_rule Obj (Functor_cat $A $B) ≡ Obj (Functor_cat $A' $B') ↪ [ $A ≡ $A'; $B ≡ $B' ];

symbol fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  τ (Obj A) → τ (Obj B);

symbol fapp1_func : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  τ (Functor (Hom_cat A X_A Y_A) (Hom_cat B (fapp0 F_AB X_A) (fapp0 F_AB Y_A)));

symbol fapp1_fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  Π (f : τ (Hom A X_A Y_A)),
  τ (Hom B (fapp0 F_AB X_A) (fapp0 F_AB Y_A));

rule fapp0 (fapp1_func $F_AB) $f ↪ fapp1_fapp0 $F_AB $f;

constant symbol Grpd_grpd : Grpd;
constant symbol Cat_grpd  : Grpd;
rule τ Grpd_grpd ↪ Grpd;
rule τ Cat_grpd  ↪ Cat;

constant symbol Grpd_cat : Cat;
rule Obj Grpd_cat ↪ Grpd_grpd;
rule τ (Obj (Hom_cat Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);

constant symbol Cat_cat : Cat;
rule Obj Cat_cat ↪ Cat_grpd;
rule Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;

assert ⊢ τ (Obj Grpd_cat) ≡ Grpd;
assert ⊢ τ (Obj Cat_cat) ≡ Cat;
assert (A B : Cat) ⊢ Hom_cat Cat_cat A B ≡ Functor_cat A B;

// Directed Cat-valued families are canonical Cat-valued functors.
injective symbol Catd_cat (K : Cat) : Cat;

injective symbol Catd (K : Cat) : Grpd
≔ Obj (Catd_cat K);

rule Functor_cat $K Cat_cat ↪ @Catd_cat $K;

unif_rule Obj (@Catd_cat $K) ≡ Obj (@Catd_cat $K') ↪ [ $K ≡ $K' ];

// Natural families of functors between directed Cat-valued families.
injective symbol Functord_cat [K : Cat] (E D : τ (Catd K)) : Cat;

injective symbol Functord [K : Cat] (E D : τ (Catd K)) : Grpd
≔ Obj (@Functord_cat K E D);

unif_rule Obj (@Functord_cat $K $E $D) ≡ Obj (@Functord_cat $K' $E' $D')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D' ];

rule Hom_cat (@Catd_cat $K) $E $D ↪ @Functord_cat $K $E $D;

symbol id_funcd [K : Cat] [E : τ (Catd K)] : τ (Functord E E);
rule @id (@Catd_cat $K) $E ↪ @id_funcd $K $E;

symbol comp_catd_fapp0 [K : Cat] [E D : τ (Catd K)] [C : τ (Catd K)]
  (FF : τ (Functord D C)) (GG : τ (Functord E D)) : τ (Functord E C);

// Stable displayed-composition head, parallel to `comp_cat_fapp0`.
rule @comp_fapp0 (@Catd_cat $K) $E $D $C $FF $GG
  ↪ @comp_catd_fapp0 $K $E $D $C $FF $GG;

rule @comp_catd_fapp0 $K $E $E $C $FF (@id_funcd $K $E)
  ↪ $FF;
rule @comp_catd_fapp0 $K $E $D $D (@id_funcd $K $D) $GG
  ↪ $GG;


// Natural families of transformations, i.e. modifications between
// directed-family functors.
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
symbol id_transfd [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : τ (@Transfd K E D FF FF);

rule @id (@Functord_cat $K $E $D) $FF
  ↪ @id_transfd $K $E $D $FF;

assert [K : Cat] ⊢ Functor_cat K Cat_cat ≡ Catd_cat K;
assert [K : Cat] (E D : τ (Catd K)) ⊢
  Hom_cat (Catd_cat K) E D ≡ Functord_cat E D;
assert [K : Cat] [E D : τ (Catd K)] (FF GG : τ (Functord E D)) ⊢
  Hom_cat (Functord_cat E D) FF GG ≡ Transfd_cat FF GG;
assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  @id (@Functord_cat K E D) FF
    ≡ @id_transfd K E D FF;

symbol id_func [A: Cat] : τ (Functor A A);
rule @id Cat_cat $A ↪ @id_func $A;
rule fapp0 (@id_func $A) $xA ↪ $xA;

symbol comp_cat_fapp0 [A B : Cat] [C : Cat]
  (F : τ (Functor B C)) (G : τ (Functor A B)) : τ (Functor A C);

rule @comp_fapp0 Cat_cat $A $B $C $F $G ↪ @comp_cat_fapp0 $A $B $C $F $G;
rule @fapp0 $A $C (@comp_cat_fapp0 $A $B $C $F $G) $x ↪ @fapp0 $B $C $F (@fapp0 $A $B $G $x);

rule @comp_fapp0 $A $Y $Y $Z $g (@id $A $Y) ↪ $g;
rule @comp_fapp0 $A $X $Z $Z (@id $A $Z) $f ↪ $f;

injective symbol Op_func : Π [A B : Cat],
  τ (Functor A B) → τ (Functor (Op_cat A) (Op_cat B));

rule Op_func (@Op_func $A $B $F) ↪ $F;
rule @fapp0 _ _ (@Op_func $A $B $F) $xA ↪ @fapp0 $A $B $F $xA;
rule @fapp1_func _ _ (@Op_func $A $B $F) $X $Y ↪ @fapp1_func $A $B $F $Y $X;
rule @Op_func _ _ (@id_func $A) ↪ @id_func (Op_cat $A);
rule @Op_func _ _ (@comp_cat_fapp0 $A $B $C $F $G)
  ↪ comp_cat_fapp0 (Op_func $F) (Op_func $G);

// Terminal category and points-as-functors are needed to derive unary homs from binary hom.
constant symbol Terminal_cat : Cat;
rule Op_cat Terminal_cat ↪ Terminal_cat;
rule Obj Terminal_cat ↪ Unit_grpd;
rule Hom_cat Terminal_cat _ _ ↪ Terminal_cat;

constant symbol Terminal_obj : τ (Obj Terminal_cat);
rule @id Terminal_cat _ ↪ Terminal_obj;
rule @comp_fapp0 Terminal_cat _ _ _ _ _ ↪ Terminal_obj;

injective symbol Terminal_func : Π (A : Cat), τ (Functor A Terminal_cat);
rule @Op_func _ _ (@Terminal_func $A) ↪ @Terminal_func (Op_cat $A);

injective symbol Obj_func : Π [Y : Cat], τ (Obj Y) → τ (Functor Terminal_cat Y);
rule fapp0 (Obj_func $y) _ ↪ $y;
rule @Op_func _ _ (@Obj_func $Y $y) ↪ @Obj_func (Op_cat $Y) $y;

symbol fapp0_func : Π [A B : Cat],
  τ (Obj A) → τ (Functor (Functor_cat A B) B);
rule fapp0 (fapp0_func $x) $F ↪ fapp0 $F $x;

// Constant functor, used by constant directed families without capping the
// hom-action too early.
symbol Const_func [A B : Cat] (b : τ (Obj B)) : τ (Functor A B);
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

// Internalized opposite as a functor in Cat: A |-> A^op.
constant symbol op : τ (Functor Cat_cat Cat_cat);
rule @fapp0 Cat_cat Cat_cat op $A ↪ Op_cat $A;
rule @fapp1_fapp0 Cat_cat Cat_cat op $A $B $F ↪ @Op_func $A $B $F;

// Internalized ordinary functor-category formation.
symbol Functor_cat_func : τ (Functor (Op_cat Cat_cat) (Functor_cat Cat_cat Cat_cat));

symbol Functor_cat_fapp0_func (A : Cat) : τ (Functor Cat_cat Cat_cat);

rule @fapp0 _ _ Functor_cat_func $A
  ↪ Functor_cat_fapp0_func $A;
rule @fapp0 Cat_cat Cat_cat (Functor_cat_fapp0_func $A) $B
  ↪ Functor_cat $A $B;

// Curried postcomposition in Cat, used to build constructor pipelines.
symbol comp_cat_cov_func : Π [X Y Z : Cat],
  Π (G : τ (Functor Y Z)),
  τ (Functor (Functor_cat X Y) (Functor_cat X Z));

rule fapp0 (@comp_cat_cov_func $X $Y $Z $G) $F
  ↪ comp_cat_fapp0 $G $F;

symbol op_val_func [Z : Cat] : τ (Functor (Catd_cat Z) (Catd_cat Z))
≔ @comp_cat_cov_func Z Cat_cat Cat_cat op;

// -------------------------------------------------------------------------------------------------
// 3. Curried internal hom
// -------------------------------------------------------------------------------------------------

symbol hom_ [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  : τ (Functor B Cat_cat);
rule @fapp0 $B Cat_cat (@hom_ $A $B $F $W) $y
  ↪ Hom_cat $A $W (@fapp0 $B $A $F $y);

// Ordinary hom-action computes by postcomposition:
// ((Hom_A(W,F-))_1 f)_0 g ↪ (F f) ∘ g.
rule fapp0 (@fapp1_fapp0 $B Cat_cat (@hom_ $A $B $F $W) $X $Y $f) $g
  ↪ comp_fapp0 (fapp1_fapp0 $F $f) $g;

symbol hom_con [A : Cat] (W : τ (Obj A)) [B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat B) Cat_cat);
rule @hom_con $A $W $B $F
  ↪ @hom_ (Op_cat $A) (Op_cat $B) (@Op_func $B $A $F) $W;

symbol hom_int [A B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat A) (Catd_cat B));

rule @fapp0 _ _ (@hom_int $A $B $F) $W
  ↪ @hom_ $A $B $F $W;

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

// -------------------------------------------------------------------------------------------------
// 4. Encoded Sigma types for object layers
// -------------------------------------------------------------------------------------------------

inductive τΣ_ [a : Grpd] (P : τ a → Grpd) : TYPE ≔
| Struct_sigma [a P] : Π (sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst)), @τΣ_ a P;
notation τΣ_ quantifier;

constant symbol Σ_ [a : Grpd] (P : τ a → Grpd) : Grpd;
notation Σ_ quantifier;
rule τ (Σ_ $P) ↪ τΣ_ $P;

injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;

injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;

// -------------------------------------------------------------------------------------------------
// 5. Ordinary transfors
// -------------------------------------------------------------------------------------------------

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
// Transformations between point functors from the terminal category are just
// arrows in the target. This implementation-discovered bridge is used by the
// late `piapp1_int_tgt_transf` projection chain: without it, the final
// `tapp0_fapp0 Terminal_obj ... -> piapp1_func` fold cannot prove subject
// reduction.
rule @Transf_cat Terminal_cat $Y (@Obj_func $Y $u) (@Obj_func $Y $v)
  ↪ Hom_cat $Y $u $v;

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

rule @tapp0_fapp0 $A $B $F $F $Y (@id (Functor_cat $A $B) $F)
  ↪ @id $B (@fapp0 $A $B $F $Y);

rule @tapp0_fapp0 $K Cat_cat $E $E $Y (@id_funcd $K $E)
  ↪ @id_func (@fapp0 $K Cat_cat $E $Y);

rule @tapp0_fapp0 $A $B $F $H $Y (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
  ↪ comp_fapp0
      (@tapp0_fapp0 $A $B $G $H $Y $η)
      (@tapp0_fapp0 $A $B $F $G $Y $ϵ);

// Reserved capped ordinary hom-action surface. It is not used by v3.2 rules
// yet. The intended computation is the projected endpoint of
// `tapp1_int_func_transf`: evaluate the internal action at ϵ, project the
// resulting transfor at X and then Y, and finally apply the resulting hom
// functor to f. Keep it abstract until the external ordinary naturality API is
// promoted.
symbol tapp1_fapp0 : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π [X Y : τ (Obj A)],
  Π (ϵ : τ (Obj (Transf_cat F G))),
  Π (f : τ (Hom A X Y)),
  τ (Hom B (fapp0 F X) (fapp0 G Y));

/*
  More-internal ordinary hom-action.

  This ports the settled v2 core without also committing to the later
  hom-action packaging heads.  The functor sends a transfor ϵ : F ⇒ G to the
  internalized action

    hom_int(id_A) ⇒ hom_int(G) ∘ F^op.
*/
symbol tapp1_int_func_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  τ (Functor
      (Transf_cat F G)
      (Transf_cat
        (@hom_int A A (@id_func A))
        (comp_cat_fapp0
          (@hom_int B A G)
          (@Op_func A B F))));

symbol tapp1_int_fapp0_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (ϵ : τ (Transf F G)),
  τ (Transf
      (@hom_int A A (@id_func A))
      (comp_cat_fapp0
        (@hom_int B A G)
        (@Op_func A B F)));

rule fapp0 (@tapp1_int_func_transf $A $B $F $G) $ϵ
  ↪ @tapp1_int_fapp0_transf $A $B $F $G $ϵ;

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

symbol fapp1_int_transf : Π [A B : Cat], Π (F : τ (Functor A B)),
  τ (Transf
      (@hom_int A A (@id_func A))
      (comp_cat_fapp0
        (@hom_int B A F)
        (@Op_func A B F)));

rule @tapp1_int_fapp0_transf $A $B $F $F (id (Functor_cat $A $B) $F)
  ↪ @fapp1_int_transf $A $B $F;

assert [A B : Cat] (F G : τ (Functor A B)) (ϵ : τ (Transf F G)) ⊢
  fapp0 (@tapp1_int_func_transf A B F G) ϵ
    ≡ @tapp1_int_fapp0_transf A B F G ϵ;

assert [A B : Cat] (F G : τ (Functor A B))
  (ϵ ϵ' : τ (Transf F G)) ⊢
  @fapp1_func _ _ (@tapp1_int_func_transf A B F G) ϵ ϵ'
    ≡ @tapp1_int_fapp1_func_transf A B F G ϵ ϵ';

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @tapp1_int_fapp0_transf A B F F (id (Functor_cat A B) F)
    ≡ @fapp1_int_transf A B F;

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  fapp0 (@tapp1_int_func_transf A B F F) (id (Functor_cat A B) F)
    ≡ @fapp1_int_transf A B F;

// -------------------------------------------------------------------------------------------------
// 6. Directed Cat-valued family constructors
// -------------------------------------------------------------------------------------------------

symbol Fibre_cat [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) : Cat
≔ @fapp0 K Cat_cat E k;

symbol Pullback_catd [A B : Cat] (E : τ (Catd B)) (F : τ (Functor A B))
  : τ (Catd A)
≔ @comp_cat_fapp0 A B Cat_cat E F;

injective symbol Const_catd (K : Cat) (A : Cat) : τ (Catd K);

rule @fapp0 $K Cat_cat (@Const_catd $K $A) $_ ↪ $A;
rule @hom_ $A $B (@Const_func $B $A $u) $w
  ↪ @Const_catd $B (Hom_cat $A $w $u);

rule @fapp1_func $K Cat_cat (@Const_catd $K $A) $x $y
  ↪ @Const_func
      (Hom_cat $K $x $y)
      (Functor_cat $A $A)
      (@id_func $A);

rule @fapp1_fapp0 $K Cat_cat (@Const_catd $K $A) $x $y $_ ↪ @id_func $A;

symbol Terminal_catd (K : Cat) : τ (Catd K)
≔ @Const_catd K Terminal_cat;

injective symbol Op_catd [K : Cat] (E : τ (Catd K)) : τ (Catd K);

rule @fapp0 $K Cat_cat (@Op_catd $K $E) $k
  ↪ Op_cat (@fapp0 $K Cat_cat $E $k);

rule @Op_catd $K (@Op_catd $K $E) ↪ $E;
rule @Op_catd $K (@Const_catd $K $A) ↪ @Const_catd $K (Op_cat $A);

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

injective symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat;

rule @Functord_cat $K (@Const_catd $K Terminal_cat) $E ↪ @Pi_cat $K $E;
rule @Pi_cat $K (@Const_catd $K $A) ↪ Functor_cat $K $A;

unif_rule Obj (@Pi_cat $K $E) ≡ Obj (@Pi_cat $K' $E') ↪ [ $K ≡ $K'; $E ≡ $E' ];

rule Hom_cat (@Pi_cat $K $E) $s $t
  ↪ @Transfd_cat $K (@Const_catd $K Terminal_cat) $E $s $t;

symbol Pi_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
rule @fapp0 (@Catd_cat $K) Cat_cat (@Pi_func $K) $E
  ↪ @Pi_cat $K $E;

symbol piapp0_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Pi_cat E) (Fibre_cat E k))
≔ comp_cat_fapp0
     (@fapp0_func Terminal_cat (Fibre_cat E k) Terminal_obj)
     (@tapp0_func K Cat_cat (@Const_catd K Terminal_cat) E k);

symbol piapp0 : Π [K : Cat], Π [E : τ (Catd K)],
  Π (s : τ (Obj (Pi_cat E))),
  Π (k : τ (Obj K)),
  τ (Obj (Fibre_cat E k))
≔ λ K E s k, @fapp0 (Pi_cat E) (Fibre_cat E k) (@piapp0_func K E k) s;

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
injective symbol Sigma_cat [K : Cat] (E : τ (Catd K)) : Cat;

injective symbol Sigma_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
rule @fapp0 (@Catd_cat $K) Cat_cat (@Sigma_func $K) $E
  ↪ @Sigma_cat $K $E;

rule τ (Obj (@Sigma_cat $K $E))
  ↪ `τΣ_ k : τ (Obj $K), Obj (Fibre_cat $E k);

injective symbol Sigma_proj1_func [K : Cat] (E : τ (Catd K))
  : τ (Functor (Sigma_cat E) K);

rule fapp0 (Sigma_proj1_func $E) (Struct_sigma $k $u) ↪ $k;

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

// -------------------------------------------------------------------------------------------------
// 8. Mixed-variance family functor
// -------------------------------------------------------------------------------------------------

symbol Functor_catd [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B : τ (Catd K))
  : τ (Catd K);

rule @fapp0 $K Cat_cat (@Functor_catd $K $A $B) $k
  ↪ Functor_cat (Fibre_cat $A $k) (Fibre_cat $B $k);

symbol Functor_catd_mix_func (K : Cat)
  : τ (Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Functor_cat (Catd_cat K) (Catd_cat K)));

symbol Functor_catd_mix_fapp0_func [K : Cat]
  (A : τ (Catd (Op_cat K)))
  : τ (Functor (Catd_cat K) (Catd_cat K));

rule @fapp0 _ _
      (@Functor_catd_mix_func $K) $A
  ↪ @Functor_catd_mix_fapp0_func $K $A;

rule @fapp0 _ _ (@Functor_catd_mix_fapp0_func $K $A) $B
  ↪ @Functor_catd $K $A $B;

symbol Hom_catd [K : Cat]
  (E : τ (Catd K))
  (X : τ (Obj (Pi_cat (Op_catd E))))
  (Y : τ (Obj (Pi_cat E)))
  : τ (Catd K);

rule @fapp0 $K Cat_cat (@Hom_catd $K $E $X $Y) $k
  ↪ Hom_cat
      (Fibre_cat $E $k)
      (@piapp0 $K (@Op_catd $K $E) $X $k)
      (@piapp0 $K $E $Y $k);

symbol Transf_catd [K : Cat]
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

symbol Edge_catd_fam [Z : Cat]
  : τ (Functor (Op_cat Z) (Catd_cat Z))
≔ comp_cat_fapp0
     (@op_val_func Z)
     (@hom_int Z Z (@id_func Z));

symbol Presheaf_catd_func (K : Cat)
  : τ (Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Catd_cat K))
≔ comp_cat_fapp0
     (@fapp0_func (Catd_cat K) (Catd_cat K) (@Const_catd K Cat_cat))
     (@Functor_catd_mix_func K);

symbol HomPresheaf_catd [Z : Cat]
  : τ (Functor Z (Catd_cat (Op_cat Z)))
≔ comp_cat_fapp0
     (@Presheaf_catd_func (Op_cat Z))
     (@Op_func (Op_cat Z) (Catd_cat Z) (@Edge_catd_fam Z));

// -------------------------------------------------------------------------------------------------
// 10. Directed homd target and internal homd category
// -------------------------------------------------------------------------------------------------

/*
  Homd architecture note:
  `Homd_source_catd`, `Homd_section_catd`, and `Homd_target_catd` name the
  intended source/target families for readability and assertions.  They are
  not used as required discriminants in the projection-rule LHSs below, because
  those positions are inferred implicit arguments and may reduce to canonical
  compound terms before matching.
*/

symbol Homd_source_catd [Z : Cat] (E : τ (Catd Z))
  : τ (Catd Z)
≔ @Op_catd Z E;

symbol Homd_section_catd [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  : τ (Catd (Op_cat Z))
≔ @Functor_catd
     (Op_cat Z)
     E
     (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x);

symbol Homd_target_catd [Z : Cat] (E : τ (Catd Z))
  : τ (Catd Z)
≔ @comp_cat_fapp0
     Z
     (Catd_cat (Op_cat Z))
     Cat_cat
     (@comp_cat_fapp0
       (Catd_cat (Op_cat Z))
       (Catd_cat (Op_cat Z))
       Cat_cat
       (@Pi_func (Op_cat Z))
       (@fapp0
         (Op_cat (Catd_cat Z))
         (Functor_cat (Catd_cat (Op_cat Z)) (Catd_cat (Op_cat Z)))
         (@Functor_catd_mix_func (Op_cat Z))
         E))
     (@HomPresheaf_catd Z);

symbol Homd_cat [Z : Cat] (E : τ (Catd Z)) : Cat
≔ @Transf_cat Z Cat_cat (@Homd_source_catd Z E) (@Homd_target_catd Z E);

symbol Homd [Z : Cat] (E : τ (Catd Z)) : Grpd
≔ Obj (@Homd_cat Z E);

// Keep homd_int constant: terminal-source behavior is exposed through stable
// projection rules below. Whole-family rewrite probes either fail by type
// mismatch, are rejected because this symbol is constant, or time out once the
// constness is removed and the rewrite is added.
constant symbol homd_int : Π [Z : Cat], Π [D E : τ (Catd Z)],
  Π (FF : τ (Functord D E)),
  τ (Functord (Op_catd E) (@Homd_target_catd Z D));

// -------------------------------------------------------------------------------------------------
// 11. Endpoint normal forms for Sigma homs
// -------------------------------------------------------------------------------------------------

symbol fib_cov_tapp0_func [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Functor (Hom_cat K x y) (Fibre_cat E y))
≔ @comp_cat_fapp0
     (Hom_cat K x y)
     (Functor_cat (Fibre_cat E x) (Fibre_cat E y))
     (Fibre_cat E y)
     (@fapp0_func (Fibre_cat E x) (Fibre_cat E y) u)
     (@fapp1_func K Cat_cat E x y);

symbol fib_cov_transf [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (@Transf K Cat_cat (@hom_ K K (@id_func K) x) E);

symbol FibCov_target_catd [K : Cat] (E : τ (Catd K)) : τ (Catd K)
≔ @hom_con
    (@Catd_cat K)
    E
    (Op_cat K)
    (@hom_int K K (@id_func K));

symbol FibCov_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Transf_cat K Cat_cat E (@FibCov_target_catd K E);

symbol FibCov [K : Cat] (E : τ (Catd K)) : Grpd
≔ Obj (@FibCov_cat K E);

constant symbol fib_cov_int : Π [K : Cat], Π (E : τ (Catd K)), τ (FibCov E);

symbol fib_cov_src_func [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  : τ (Functor
      (Fibre_cat E x)
      (@Transf_cat K Cat_cat (@hom_ K K (@id_func K) x) E));

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

symbol fib_cov_tapp0_fapp0 [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Fibre_cat E y))
≔ @fapp0
     (Hom_cat K x y)
     (Fibre_cat E y)
     (@fib_cov_tapp0_func K E x y u)
     f;

// General endpoint notation for dependent homs along a displayed functor. The
// old one-family endpoint is the identity-family specialization.
symbol homd_ [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  (v : τ (Obj (Fibre_cat D y)))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat)
≔ @hom_con
     (Fibre_cat E y)
     (@fapp0
       (Fibre_cat D y)
       (Fibre_cat E y)
       (@tapp0_fapp0 Z Cat_cat D E y FF)
       v)
     (Hom_cat Z x y)
     (@fib_cov_tapp0_func Z E x y u);

// General first projection of `homd_int`: externalize x and the source fibre
// object in E, while the probe family D remains internal.
symbol homd_src_funcd [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  : τ (Functor
        (Fibre_cat (@Op_catd Z E) x)
        (Pi_cat (@Homd_section_catd Z D x)));

// Component functor after projecting the fully internal homd object at x.
symbol homd_src_func [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  : τ (Functor
        (Fibre_cat (@Homd_source_catd Z E) x)
        (Pi_cat (@Homd_section_catd Z E x)));

rule @homd_src_funcd $Z $E $E (@id_funcd $Z $E) $x
  ↪ @homd_src_func $Z $E $x;

// First projection fold. The source and target family arguments are
// deliberately `_`: their canonical forms contain reducible expressions such
// as `fapp0 (op_val_func Z) E` and `Homd_target_catd E`.  The Transf_cat
// unification helper above supplies the needed endpoint information.
rule @tapp0_fapp0
      $Z
      Cat_cat
      _
      _
      $x
      (@homd_int $Z $D $E $FF)
  ↪ @homd_src_funcd $Z $D $E $FF $x;

// General source-fixed projection after evaluating the component functor at u.
symbol homd_src_secd [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (@Homd_section_catd Z D x)));

// Source-fixed projection after evaluating the identity-specialized component
// functor at u.
symbol homd_src_sec [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (@Homd_section_catd Z E x)));

rule @homd_src_secd $Z $E $E (@id_funcd $Z $E) $x $u
  ↪ @homd_src_sec $Z $E $x $u;

// Second projection fold: externalize x,u and keep the y,v endpoint internal.
rule fapp0 (@homd_src_funcd $Z $D $E $FF $x) $u
  ↪ @homd_src_secd $Z $D $E $FF $x $u;

// Identity-specialized compatibility fold retained for stable old normal
// forms and assertions.
rule fapp0 (@homd_src_func $Z $E $x) $u
  ↪ @homd_src_sec $Z $E $x $u;

// Terminal-source normal form for the first homd projection. This is the
// projected form needed by Pi-action; it avoids a broad whole-family homd_int
// rewrite while exposing the unique terminal source object.
rule @homd_src_func $Z (@Const_catd $Z Terminal_cat) $x
  ↪ @Obj_func
      (Pi_cat (@Homd_section_catd $Z (@Const_catd $Z Terminal_cat) $x))
      (@homd_src_sec $Z (@Const_catd $Z Terminal_cat) $x Terminal_obj);

// General inner endpoint functor after projecting the source-fixed section at y.
symbol homd_tgt_funcd [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  : τ (Functor
        (Fibre_cat D y)
        (Fibre_cat
          (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x)
          y));

// Inner endpoint functor after projecting the identity-specialized
// source-fixed section at y.
symbol homd_tgt_func [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  : τ (Functor
        (Fibre_cat E y)
        (Fibre_cat
          (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x)
          y));

rule @homd_tgt_funcd $Z $E $E (@id_funcd $Z $E) $x $u $y
  ↪ @homd_tgt_func $Z $E $x $u $y;

// Terminal-source normal form for the inner endpoint functor. Applying the
// resulting Obj_func at Terminal_obj joins with the generic fapp0 fold through
// homd_ and the constant terminal endpoint cascade.
rule @homd_tgt_func $Z (@Const_catd $Z Terminal_cat) $x Terminal_obj $y
  ↪ @Obj_func
      (Fibre_cat
        (@fapp0 $Z (Catd_cat (Op_cat $Z)) (@HomPresheaf_catd $Z) $x)
        $y)
      (@Terminal_catd (Op_cat (Hom_cat $Z $x $y)));

// Terminal-source normal form for the generalized inner endpoint. This exposes
// the same homd-valued family used by piapp1_func without adding a broad
// whole-family homd_int rewrite.
rule @homd_tgt_funcd $Z (@Const_catd $Z Terminal_cat) $E $s $x $u $y
  ↪ @Obj_func
      (Fibre_cat
        (@fapp0 $Z (Catd_cat (Op_cat $Z)) (@HomPresheaf_catd $Z) $x)
        $y)
      (@homd_
        $Z
        $E
        $E
        (@id_funcd $Z $E)
        $x
        $u
        $y
        (@piapp0 $Z $E $s $y));

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
      (@homd_src_secd $Z $D $E $FF $x $u)
  ↪ @Obj_func
      (Fibre_cat (@Homd_section_catd $Z $D $x) $y)
      (@homd_tgt_funcd $Z $D $E $FF $x $u $y);

// Identity-specialized compatibility fold retained for stable old normal
// forms and assertions.
rule @tapp0_fapp0
      (Op_cat $Z)
      Cat_cat
      (@Const_catd (Op_cat $Z) Terminal_cat)
      _
      $y
      (@homd_src_sec $Z $E $x $u)
  ↪ @Obj_func
      (Fibre_cat (@Homd_section_catd $Z $E $x) $y)
      (@homd_tgt_func $Z $E $x $u $y);

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
rule fapp0 (@homd_tgt_funcd $Z $D $E $FF $x $u $y) $v
  ↪ @homd_ $Z $D $E $FF $x $u $y $v;

// Identity-specialized compatibility fold retained for stable old normal
// forms and assertions.
rule fapp0 (@homd_tgt_func $Z $E $x $u $y) $v
  ↪ @homd_ $Z $E $E (@id_funcd $Z $E) $x $u $y $v;

rule Hom_cat (@Sigma_cat $K $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_cat
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (@homd_ $K $E $E (@id_funcd $K $E) $x $u $y $v));

// -------------------------------------------------------------------------------------------------
// 12. Section action over dependent homs
// -------------------------------------------------------------------------------------------------

/*
  Full section action over a base arrow.

  `piapp1_func` is the section-level package over the base-arrow category.
  The capped object component is defined by ordinary section evaluation, so it
  remains iterable through `Pi_cat` rather than becoming only an object-level
  shortcut. The terminal-specialization fold from displayed internal action is
  installed later, after the concrete displayed-composition projection it needs.
*/
symbol piapp1_src_obj [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Obj (Fibre_cat E y))
≔ @fib_cov_tapp0_fapp0 K E x y f (@piapp0 K E s x);

symbol piapp1_func [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  : τ (Obj (Pi_cat
      (@homd_
        K
        E
        E
        (@id_funcd K E)
        x
        (@piapp0 K E s x)
        y
        (@piapp0 K E s y))));

symbol piapp1_fapp0 [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Obj
      (@fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@homd_
          K
          E
          E
          (@id_funcd K E)
          x
          (@piapp0 K E s x)
          y
          (@piapp0 K E s y))
        f))
≔ @piapp0
     (Op_cat (Hom_cat K x y))
     (@homd_
       K
       E
       E
       (@id_funcd K E)
       x
       (@piapp0 K E s x)
       y
       (@piapp0 K E s y))
     (@piapp1_func K E s x y)
     f;

rule @fapp0
      (Op_cat (Hom_cat $K $x $y))
      (Hom_cat $A (@fapp0 $K $A $s $x) (@fapp0 $K $A $s $y))
      (@piapp1_func $K (@Const_catd $K $A) $s $x $y)
      $f
  ↪ @fapp1_fapp0 $K $A $s $x $y $f;

// -------------------------------------------------------------------------------------------------
// 13. Internal displayed hom-action heads
// -------------------------------------------------------------------------------------------------

symbol tdapp1_int_func_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  τ (Functor
      (@Transfd_cat K E D FF GG)
      (@Transfd_cat
        K
        (@Op_catd K E)
        (@Homd_target_catd K E)
        (@homd_int K E E (@id_funcd K E))
        (@comp_catd_fapp0
          K
          (@Op_catd K E)
          (@Op_catd K D)
          (@Homd_target_catd K E)
          (@homd_int K E D GG)
          (@Op_funcd K E D FF))));

symbol tdapp1_int_fapp0_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  Π (ϵ : τ (@Transfd K E D FF GG)),
  τ (@Transfd
      K
      (@Op_catd K E)
      (@Homd_target_catd K E)
      (@homd_int K E E (@id_funcd K E))
      (@comp_catd_fapp0
        K
        (@Op_catd K E)
        (@Op_catd K D)
        (@Homd_target_catd K E)
        (@homd_int K E D GG)
        (@Op_funcd K E D FF)));

rule fapp0 (@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ
  ↪ @tdapp1_int_fapp0_transfd $K $E $D $FF $GG $ϵ;

symbol tdapp1_int_fapp1_func_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  Π (ϵ ϵ' : τ (@Transfd K E D FF GG)),
  τ (Functor
      (Hom_cat (@Transfd_cat K E D FF GG) ϵ ϵ')
      (Hom_cat
        (@Transfd_cat
          K
          (@Op_catd K E)
          (@Homd_target_catd K E)
          (@homd_int K E E (@id_funcd K E))
          (@comp_catd_fapp0
            K
            (@Op_catd K E)
            (@Op_catd K D)
            (@Homd_target_catd K E)
            (@homd_int K E D GG)
            (@Op_funcd K E D FF)))
        (@tdapp1_int_fapp0_transfd K E D FF GG ϵ)
        (@tdapp1_int_fapp0_transfd K E D FF GG ϵ')));

rule @fapp1_func _ _ (@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ $ϵ'
  ↪ @tdapp1_int_fapp1_func_transfd $K $E $D $FF $GG $ϵ $ϵ';

symbol fdapp1_int_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π (FF : τ (Functord E D)),
  τ (@Transfd
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
        (@Op_funcd K E D FF)));

// Internal Pi-action witness: terminal-source specialization of the internal
// displayed hom-action. Projection to `piapp1_func` is installed later through
// stable intermediate heads.
symbol piapp1_int [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  : τ (@Transfd
      K
      (@Op_catd K (@Const_catd K Terminal_cat))
      (@Homd_target_catd K (@Const_catd K Terminal_cat))
      (@homd_int
        K
        (@Const_catd K Terminal_cat)
        (@Const_catd K Terminal_cat)
        (@id_funcd K (@Const_catd K Terminal_cat)))
      (@comp_catd_fapp0
        K
        (@Op_catd K (@Const_catd K Terminal_cat))
        (@Op_catd K E)
        (@Homd_target_catd K (@Const_catd K Terminal_cat))
        (@homd_int K (@Const_catd K Terminal_cat) E s)
        (@Op_funcd K (@Const_catd K Terminal_cat) E s)));

rule @fdapp1_int_transfd
      $K
      (@Const_catd $K Terminal_cat)
      $E
      $s
  ↪ @piapp1_int $K $E $s;

// Identity-specialization fold for the internal displayed hom-action.
rule @tdapp1_int_fapp0_transfd $K $E $D $FF $FF
      (@id_transfd $K $E $D $FF)
  ↪ @fdapp1_int_transfd $K $E $D $FF;

// -------------------------------------------------------------------------------------------------
// 14. Derived displayed component notation
// -------------------------------------------------------------------------------------------------

/*
  `tdapp0_func` and `tdapp0_fapp0` are stable projection heads for the
  displayed component of a displayed transfor. This mirrors emdash2: readable
  fibre notation below remains definitional, while rewrite rules attach to
  these primitive heads.
*/
symbol tdapp0_func [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (z : τ (Obj K))
  : τ (Functor
      (@Transfd_cat K E D FF GG)
      (@Transf_cat
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@tapp0_fapp0 K Cat_cat E D z FF)
        (@tapp0_fapp0 K Cat_cat E D z GG)));

symbol tdapp0_fapp0 [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (z : τ (Obj K))
  (ϵ : τ (@Transfd K E D FF GG))
  : τ (@Transf
      (Fibre_cat E z)
      (Fibre_cat D z)
      (@tapp0_fapp0 K Cat_cat E D z FF)
      (@tapp0_fapp0 K Cat_cat E D z GG));

rule fapp0 (@tdapp0_func $K $E $D $FF $GG $z) $ϵ
  ↪ @tdapp0_fapp0 $K $E $D $FF $GG $z $ϵ;

// Readable derived fibre-level notation. These are definitions over ordinary
// transfor projection; they are not additional kernel rewrite heads.
symbol Fibre_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (z : τ (Obj K))
  : τ (Functor (Fibre_cat E z) (Fibre_cat D z))
≔ @tapp0_fapp0 K Cat_cat E D z FF;

symbol Fibre_transf [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (@Transfd K E D FF GG))
  (z : τ (Obj K))
  : τ (@Transf
      (Fibre_cat E z)
      (Fibre_cat D z)
      (@Fibre_func K E D FF z)
      (@Fibre_func K E D GG z))
≔ @tdapp0_fapp0 K E D FF GG z ϵ;

symbol Fibre_transf_app [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (@Transfd K E D FF GG))
  (z : τ (Obj K))
  (u : τ (Obj (Fibre_cat E z)))
  : τ (Hom
      (Fibre_cat D z)
      (@fapp0 (Fibre_cat E z) (Fibre_cat D z) (@Fibre_func K E D FF z) u)
      (@fapp0 (Fibre_cat E z) (Fibre_cat D z) (@Fibre_func K E D GG z) u))
≔ @tapp0_fapp0
     (Fibre_cat E z)
     (Fibre_cat D z)
     (@Fibre_func K E D FF z)
     (@Fibre_func K E D GG z)
     u
     (@Fibre_transf K E D FF GG ϵ z);

// Derived fibre projection of the internal displayed hom-action. This is a
// named projection of `fdapp1_int_transfd`, not a separate external `fdapp1`
// surface operation.
symbol fdapp1_int_fibre_transf [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  : τ (@Transf
      (Fibre_cat (@Op_catd K E) x)
      (Fibre_cat (@Homd_target_catd K E) x)
      (@Fibre_func
        K
        (@Op_catd K E)
        (@Homd_target_catd K E)
        (@homd_int K E E (@id_funcd K E))
        x)
      (@Fibre_func
        K
        (@Op_catd K E)
        (@Homd_target_catd K E)
        (@comp_catd_fapp0
          K
          (@Op_catd K E)
          (@Op_catd K D)
          (@Homd_target_catd K E)
          (@homd_int K E D FF)
          (@Op_funcd K E D FF))
        x))
≔ @Fibre_transf
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
     x;

symbol fdapp1_int_fibre_app [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat (@Op_catd K E) x)))
  : τ (Hom
      (Fibre_cat (@Homd_target_catd K E) x)
      (@fapp0
        (Fibre_cat (@Op_catd K E) x)
        (Fibre_cat (@Homd_target_catd K E) x)
        (@Fibre_func
          K
          (@Op_catd K E)
          (@Homd_target_catd K E)
          (@homd_int K E E (@id_funcd K E))
          x)
        u)
      (@fapp0
        (Fibre_cat (@Op_catd K E) x)
        (Fibre_cat (@Homd_target_catd K E) x)
        (@Fibre_func
          K
          (@Op_catd K E)
          (@Homd_target_catd K E)
          (@comp_catd_fapp0
            K
            (@Op_catd K E)
            (@Op_catd K D)
            (@Homd_target_catd K E)
            (@homd_int K E D FF)
            (@Op_funcd K E D FF))
          x)
        u))
≔ @Fibre_transf_app
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
     u;

// -------------------------------------------------------------------------------------------------
// 15. Generic Sigma/Pi weakening helpers
// -------------------------------------------------------------------------------------------------

// Generic Sigma/Pi weakening/evaluation helpers. These reintroduce the stable
// parts of the v3 backlog whose beta assertions are now robust.
injective symbol sigma_intro_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord E (@Const_catd K (@Sigma_cat K E)));

injective symbol sigma_intro_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Fibre_cat E k) (Sigma_cat E));

rule @tapp0_fapp0
      $K
      Cat_cat
      $E
      _
      $k
      (@sigma_intro_transf $K $E)
  ↪ @sigma_intro_func $K $E $k;

rule fapp0
      (@sigma_intro_func $K $E $k)
      $u
  ↪ Struct_sigma $k $u;

symbol pi_eval_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord (@Const_catd K (@Pi_cat K E)) E);

rule @tapp0_fapp0
      $K
      Cat_cat
      (@Const_catd $K (@Pi_cat $K $E))
      $E
      $k
      (@pi_eval_transf $K $E)
  ↪ @piapp0_func $K $E $k;

symbol const_section_func (K : Cat) (A : Cat)
  : τ (Functor A (@Pi_cat K (@Const_catd K A)));

rule @fapp0
      $A
      _
      (@const_section_func $K $A)
      $a
  ↪ @Const_func $K $A $a;

symbol section_pullback_func [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  : τ (Functor (@Pi_cat B E) (@Pi_cat A (@Pullback_catd A B E F)));

symbol section_pullback_sec [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Pi_cat B E)))
  : τ (Obj (@Pi_cat A (@Pullback_catd A B E F)));

rule @fapp0
      (@Pi_cat $B $E)
      _
      (@section_pullback_func $A $B $F $E)
      $s
  ↪ @section_pullback_sec $A $B $F $E $s;

rule @tapp0_fapp0
      $A
      Cat_cat
      (@Const_catd $A Terminal_cat)
      _
      $a
      (@section_pullback_sec $A $B $F $E $s)
  ↪ @Obj_func
      (Fibre_cat (@Pullback_catd $A $B $E $F) $a)
      (@piapp0 $B $E $s (@fapp0 $A $B $F $a));

// -------------------------------------------------------------------------------------------------
// 16. Regression assertions for the mixed-variance skeleton
// -------------------------------------------------------------------------------------------------

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

assert [K : Cat] (A : Cat)
  (a : τ (Obj A))
  (k : τ (Obj K)) ⊢
  @piapp0
    K
    (@Const_catd K A)
    (@fapp0 A (@Pi_cat K (@Const_catd K A)) (@const_section_func K A) a)
    k
    ≡ a;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (Pi_cat E))) ⊢
  @fapp0
    (@Pi_cat B E)
    (@Pi_cat A (@Pullback_catd A B E F))
    (@section_pullback_func A B F E)
    s
    ≡ @section_pullback_sec A B F E s;

assert [A B : Cat] (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (Pi_cat E)))
  (a : τ (Obj A)) ⊢
  @piapp0
    A
    (@Pullback_catd A B E F)
    (@fapp0
      (@Pi_cat B E)
      (@Pi_cat A (@Pullback_catd A B E F))
      (@section_pullback_func A B F E)
      s)
    a
    ≡ @piapp0 B E s (@fapp0 A B F a);

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Sigma_func K) E ≡ Sigma_cat E;

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D)) ⊢
  @fapp1_fapp0 (Catd_cat K) Cat_cat (@Sigma_func K) E D η
    ≡ @sigma_map_func K E D η;

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ≡ k;

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat (Functor_catd A B) k
    ≡ Functor_cat (Fibre_cat A k) (Fibre_cat B k);

assert [K : Cat] (A : τ (Catd (Op_cat K))) (B : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) (Catd_cat K)
    (@fapp0
      (Op_cat (Catd_cat (Op_cat K)))
      (Functor_cat (Catd_cat K) (Catd_cat K))
      (@Functor_catd_mix_func K)
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

assert [Z : Cat] (x : τ (Obj (Op_cat Z))) (y : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat
    (@fapp0 (Op_cat Z) (Catd_cat Z) (@Edge_catd_fam Z) x)
    y
    ≡ Op_cat (Hom_cat Z x y);

assert [Z : Cat] (x : τ (Obj Z)) (y : τ (Obj (Op_cat Z))) ⊢
  Fibre_cat (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x) y
    ≡ Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat;

assert [Z : Cat] (E : τ (Catd Z)) ⊢
  @Homd_source_catd Z E ≡ @Op_catd Z E;

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @Homd_section_catd Z E x
    ≡ @Functor_catd
        (Op_cat Z)
        E
        (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x);

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_catd Z E) x
    ≡ Pi_cat
        (Functor_catd
          E
          (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x));

assert [Z : Cat] (E : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_catd Z E) x
    ≡ Pi_cat (@Homd_section_catd Z E x);

assert [Z : Cat] (E : τ (Catd Z)) ⊢
  @Homd_cat Z E
    ≡ @Transf_cat Z Cat_cat
        (@Op_catd Z E)
        (@Homd_target_catd Z E);

assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  Fibre_cat (@FibCov_target_catd K E) x
    ≡ @Transf_cat K Cat_cat (@hom_ K K (@id_func K) x) E;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @FibCov_cat K E
    ≡ @Transf_cat K Cat_cat E (@FibCov_target_catd K E);

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
  @fdapp1_int_transfd K (@Const_catd K Terminal_cat) E s
    ≡ @piapp1_int K E s;

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E))) ⊢
  @tdapp1_int_fapp0_transfd
    K
    (@Const_catd K Terminal_cat)
    E
    s
    s
    (@id_transfd K (@Const_catd K Terminal_cat) E s)
    ≡ @fdapp1_int_transfd K (@Const_catd K Terminal_cat) E s;

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E))) ⊢
  @tdapp1_int_fapp0_transfd
    K
    (@Const_catd K Terminal_cat)
    E
    s
    s
    (@id_transfd K (@Const_catd K Terminal_cat) E s)
    ≡ @piapp1_int K E s;

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

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K)) ⊢
  @fdapp1_int_fibre_transf K E D FF x
    ≡ @Fibre_transf
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
        x;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat (@Op_catd K E) x))) ⊢
  @fdapp1_int_fibre_app K E D FF x u
    ≡ @Fibre_transf_app
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
        u;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Op_catd Z E)
    (@Homd_target_catd Z D)
    x
    (@homd_int Z D E FF)
    ≡ @homd_src_funcd Z D E FF x;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z)) ⊢
  @Fibre_func
    Z
    (@Op_catd Z E)
    (@Homd_target_catd Z D)
    (@homd_int Z D E FF)
    x
    ≡ @homd_src_funcd Z D E FF x;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat (@Op_catd Z E) x))) ⊢
  @fapp0
    (Fibre_cat (@Op_catd Z E) x)
    (Fibre_cat (@Homd_target_catd Z D) x)
    (@Fibre_func Z (@Op_catd Z E) (@Homd_target_catd Z D) (@homd_int Z D E FF) x)
    u
    ≡ @homd_src_secd Z D E FF x u;

// Regression for the `homd_int` first projection. The rule itself keeps the
// source/target family arguments implicit; this assertion may spell them out
// because it is not a rewrite-pattern LHS.
assert [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@Homd_source_catd Z E)
    (@Homd_target_catd Z E)
    x
    (@homd_int Z E E (@id_funcd Z E))
    ≡ @homd_src_func Z E x;

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D)) ⊢
  fapp0 (@tdapp1_int_func_transfd K E D FF FF)
    (@id (@Functord_cat K E D) FF)
    ≡ @fdapp1_int_transfd K E D FF;

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_src_funcd Z D E FF x) u
    ≡ @homd_src_secd Z D E FF x u;

assert [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_src_func Z E x) u
    ≡ @homd_src_sec Z E x u;

assert [K : Cat] (x : τ (Obj K)) ⊢
  @homd_src_func K (@Const_catd K Terminal_cat) x
    ≡ @Obj_func
        (Pi_cat (@Homd_section_catd K (@Const_catd K Terminal_cat) x))
        (@homd_src_sec K (@Const_catd K Terminal_cat) x Terminal_obj);

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
        (Pi_cat (@Homd_section_catd K (@Const_catd K Terminal_cat) x))
        (@homd_src_sec K (@Const_catd K Terminal_cat) x Terminal_obj);

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat Z)
    (@Functor_catd
      (Op_cat Z)
      D
      (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x))
    (@homd_src_secd Z D E FF x u)
    y
    ≡ @homd_tgt_funcd Z D E FF x u y;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @piapp0
    (Op_cat Z)
    (@Functor_catd
      (Op_cat Z)
      E
      (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x))
    (@homd_src_sec Z E x u)
    y
    ≡ @homd_tgt_func Z E x u y;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  fapp0 (@homd_tgt_func Z E x u y) v
    ≡ @homd_ Z E E (@id_funcd Z E) x u y v;

assert [K : Cat] (x y : τ (Obj K)) ⊢
  @homd_tgt_func K (@Const_catd K Terminal_cat) x Terminal_obj y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd K) x)
          y)
        (@Terminal_catd (Op_cat (Hom_cat K x y)));

assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @homd_tgt_funcd K (@Const_catd K Terminal_cat) E s x u y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd K) x)
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
    (@Homd_section_catd K (@Const_catd K Terminal_cat) x)
    (@homd_src_secd K (@Const_catd K Terminal_cat) E s x u)
    y
    ≡ @Obj_func
        (Fibre_cat
          (@fapp0 K (Catd_cat (Op_cat K)) (@HomPresheaf_catd K) x)
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
  fapp0 (@homd_tgt_funcd K (@Const_catd K Terminal_cat) E s x u y) Terminal_obj
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
      (@Homd_section_catd K (@Const_catd K Terminal_cat) x)
      (@homd_src_secd
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
    (@homd_tgt_func K (@Const_catd K Terminal_cat) x Terminal_obj y)
    Terminal_obj
    ≡ @Terminal_catd (Op_cat (Hom_cat K x y));

assert [Z : Cat] (D E : τ (Catd Z)) (FF : τ (Functord D E))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  fapp0 (@homd_tgt_funcd Z D E FF x u y) v
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

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (f : τ (Hom K x y)) ⊢
  @fapp0 (Hom_cat K x y) (Fibre_cat E y)
    (@fib_cov_tapp0_func K E x y u)
    f
    ≡ @fib_cov_tapp0_fapp0 K E x y f u;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x))) ⊢
  @fib_cov_tapp0_func K (@Const_catd K A) x y u
    ≡ @Const_func (Hom_cat K x y) A u;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (f : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x))) ⊢
  @fib_cov_tapp0_fapp0 K (@Const_catd K A) x y f u
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
        (@fib_cov_tapp0_fapp0 K E x y f u)
        v;

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_src_obj K E s x y f
    ≡ @fib_cov_tapp0_fapp0 K E x y f (@piapp0 K E s x);

assert [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_
      K
      E
      E
      (@id_funcd K E)
      x
      (@piapp0 K E s x)
      y
      (@piapp0 K E s y))
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
    ≡ @piapp0
        (Op_cat (Hom_cat K x y))
        (@homd_
          K
          E
          E
          (@id_funcd K E)
          x
          (@piapp0 K E s x)
          y
          (@piapp0 K E s y))
        (@piapp1_func K E s x y)
        f;

assert [K : Cat] (A : Cat)
  (s : τ (Obj (Pi_cat (Const_catd K A))))
  (x y : τ (Obj K))
  (f : τ (Hom K x y)) ⊢
  @piapp1_fapp0 K (@Const_catd K A) s x y f
    ≡ @fapp1_fapp0 K A s x y f;

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

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D)) ⊢
  @comp_cat_fapp0 (@Sigma_cat K E) (@Sigma_cat K D) K
    (@Sigma_proj1_func K D)
    (@sigma_map_func K E D η)
    ≡ @Sigma_proj1_func K E;

// Late displayed-composition fibre projection. Early insertion near the
// projection-rule block caused timeout during earlier probes; placed here it
// supports the concrete piapp1 target-object cascade without using a composite
// capped bridge as a rewrite LHS.
rule @tapp0_fapp0
      $K
      Cat_cat
      $E
      $C
      $x
      (@comp_catd_fapp0 $K $E $D $C $FF $GG)
  ↪ @comp_cat_fapp0
      (Fibre_cat $E $x)
      (Fibre_cat $D $x)
      (Fibre_cat $C $x)
      (@tapp0_fapp0 $K Cat_cat $D $C $x $FF)
      (@tapp0_fapp0 $K Cat_cat $E $D $x $GG);

// Stable projection chain from the internal dependent pi transfor to the
// external piapp1 package. The intermediate heads avoid rewriting over
// reducible fibre abbreviations such as `Fibre_transf_app`.
symbol piapp1_int_src_transf [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x : τ (Obj K))
  : τ (Transf
      (Obj_func
        (homd_src_sec (Const_catd K Terminal_cat) x Terminal_obj))
      (comp_cat_fapp0
        (@homd_src_funcd K (@Const_catd K Terminal_cat) E s x)
        (Op_func
          (@tapp0_fapp0
            K
            Cat_cat
            (@Const_catd K Terminal_cat)
            E
            x
            s))));

symbol piapp1_int_src_app [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x : τ (Obj K))
  : τ (Hom
      (Pi_cat (Homd_section_catd (Const_catd K Terminal_cat) x))
      (homd_src_sec (Const_catd K Terminal_cat) x Terminal_obj)
      (@homd_src_secd
        K
        (@Const_catd K Terminal_cat)
        E
        s
        x
        (@piapp0 K E s x)));

symbol piapp1_int_tgt_transf [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  : τ (Transf
      (@Obj_func
        (Functor_cat Terminal_cat (Catd_cat (Op_cat (Hom_cat K x y))))
        (Obj_func
          (Const_catd (Op_cat (Hom_cat K x y)) Terminal_cat)))
      (@Obj_func
        (Functor_cat Terminal_cat (Catd_cat (Op_cat (Hom_cat K x y))))
        (Obj_func
          (@homd_
            K
            E
            E
            (@id_funcd K E)
            x
            (@piapp0 K E s x)
            y
            (@piapp0 K E s y)))));

rule tdapp0_fapp0
      $x
      (@piapp1_int $K $E $s)
  ↪ @piapp1_int_src_transf $K $E $s $x;

rule tapp0_fapp0
      Terminal_obj
      (@piapp1_int_src_transf $K $E $s $x)
  ↪ @piapp1_int_src_app $K $E $s $x;

rule tdapp0_fapp0
      $y
      (@piapp1_int_src_app $K $E $s $x)
  ↪ @piapp1_int_tgt_transf $K $E $s $x $y;

rule @tapp0_fapp0
      Terminal_cat
      _
      (Obj_func
        (Obj_func
          _))
      (Obj_func
        (Obj_func
          _))
      Terminal_obj
      (@piapp1_int_tgt_transf $K $E $s $x $y)
  ↪ @piapp1_func $K $E $s $x $y;

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
    ≡ @homd_src_secd
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
      (@Homd_section_catd K (@Const_catd K Terminal_cat) x)
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
