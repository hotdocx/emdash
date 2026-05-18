/*
  m- / emdash3.1
  Active directed-family mixed-variance v3 architecture.

  This file is the current v3 source file described in
  reports/REPORT_EMDASH_V3_CONSOLIDATED.md.  It uses directed Cat-valued
  families directly:

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
    - `homd_int E`, after projection at x,u,y,v, normalizes through
      `homd_src_func`, `homd_src_sec`, `homd_tgt_func`, then the endpoint `homd_`.

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
      `HomPresheaf_catd ...`, or `Homd_target_catd ...`.
    - Prefer small projection rules with stable heads over one large nested
      redex.  The homd endpoint is deliberately split into `tapp0_fapp0`,
      `fapp0`, `piapp0`, and `fapp0` folds for this reason.

  Stable heads and unification helpers:
    - Stable heads are the intended normal forms for operations that later
      rules need to recognize (`comp_cat_fapp0`, `fib_cov_tapp0_fapp0`,
      `tapp0_fapp0`, `homd_src_func`, `homd_src_sec`, `homd_tgt_func`).
    - Controlled `Obj`-inversion unification rules for chosen heads
      (`Hom_cat`, `Functor_cat`, `Transf_cat`, `Fibre_cat`) are elaboration
      aids.  They are not semantic claims that `Obj` is globally injective.
    - If a concrete constructor does not reduce early enough and needs one of
      these unification helpers, that is usually a signal to add a computation
      rule or introduce a smaller stable head.

  Omega-friendly normalization:
    - Prefer functor-level folds over capped pointwise rewrites when the result
      must remain iterable to higher cells.  A rule whose RHS is just
      `fapp0 (...) cell` computes one selected cell but can lose the functor
      object that would support another hom-action.
    - Use pointwise endpoint heads only when the current construction genuinely
      needs an endpoint.  Here `homd_` is such an endpoint: its object-action
      computes to the sigma-hom formula
      `Hom(E[y])(fib_cov_tapp0_fapp0 E f u, v)`, while its functor action
      delegates to the semantic `hom_con` endpoint.

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
  Maintenance inventory (v3.1)

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
      both `Transf_cat (Terminal_catd K) E` and
      `Functord_cat (Terminal_catd K) E`.
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
    - `tapp1_int_func_transf` / `fapp1_int_transf`: ordinary internal
      hom-action heads ported from v2.  The displayed analogues are deferred
      until the generalized `homd_int` arity is settled.
    - Generic Sigma/Pi weakening helpers are deferred until the directed-family
      core has enough stable beta assertions.
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

symbol Hom (A : Cat) (X_A Y_A : τ (Obj A)) : Grpd
≔ Obj (Hom_cat A X_A Y_A);

/*
  Inference-helper policy:
  These unification rules are local elaboration aids for chosen heads such as
  `Hom_cat`, `Functor_cat`, and `Transf_cat`. They should be read as controlled
  "associativity of Obj" hints, not as global semantic injectivity claims for
  arbitrary category constructors.
*/
unif_rule Obj (Hom_cat $A $X $Y) ≡ Obj (Hom_cat $A' $X' $Y') ↪ [ $A ≡ $A'; $X ≡ $X'; $Y ≡ $Y' ];
unif_rule Hom $A $X $Y ≡ Hom $A' $X' $Y' ↪ [ $A ≡ $A'; $X ≡ $X'; $Y ≡ $Y' ];

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

symbol Functor_cat : Π (A B : Cat), Cat;

symbol Functor (A B : Cat) : Grpd
≔ Obj (Functor_cat A B);

unif_rule Functor $A $B ≡ Functor $A' $B' ↪ [ $A ≡ $A'; $B ≡ $B' ];
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
symbol Catd_cat (K : Cat) : Cat;

symbol Catd (K : Cat) : Grpd
≔ Obj (Catd_cat K);

rule Functor_cat $K Cat_cat ↪ @Catd_cat $K;

unif_rule Catd $K ≡ Catd $K' ↪ [ $K ≡ $K' ];
unif_rule Obj (@Catd_cat $K) ≡ Obj (@Catd_cat $K') ↪ [ $K ≡ $K' ];

// Natural families of functors between directed Cat-valued families.
symbol Functord_cat [K : Cat] (E D : τ (Catd K)) : Cat;

symbol Functord [K : Cat] (E D : τ (Catd K)) : Grpd
≔ Obj (@Functord_cat K E D);

unif_rule Functord $E $D ≡ Functord $E' $D' ↪ [ $E ≡ $E'; $D ≡ $D' ];
unif_rule Obj (@Functord_cat $K $E $D) ≡ Obj (@Functord_cat $K' $E' $D')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D' ];

rule Hom_cat (@Catd_cat $K) $E $D ↪ @Functord_cat $K $E $D;

symbol id_funcd [K : Cat] [E : τ (Catd K)] : τ (Functord E E);
rule @id (@Catd_cat $K) $E ↪ @id_funcd $K $E;

symbol comp_catd_fapp0 [K : Cat] [E D : τ (Catd K)] [C : τ (Catd K)]
  (FF : τ (Functord D C)) (GG : τ (Functord E D)) : τ (Functord E C)
≔ @comp_fapp0 (@Catd_cat K) E D C FF GG;

// Natural families of transformations, i.e. modifications between
// directed-family functors.
symbol Transfd_cat [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D)) : Cat;

symbol Transfd [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D)) : Grpd
≔ Obj (@Transfd_cat K E D FF GG);

unif_rule Transfd $FF $GG ≡ Transfd $FF' $GG' ↪ [ $FF ≡ $FF'; $GG ≡ $GG' ];
unif_rule Obj (@Transfd_cat $K $E $D $FF $GG) ≡ Obj (@Transfd_cat $K' $E' $D' $FF' $GG')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D'; $FF ≡ $FF'; $GG ≡ $GG' ];

rule Hom_cat (@Functord_cat $K $E $D) $FF $GG
  ↪ @Transfd_cat $K $E $D $FF $GG;

assert [K : Cat] ⊢ Functor_cat K Cat_cat ≡ Catd_cat K;
assert [K : Cat] (E D : τ (Catd K)) ⊢
  Hom_cat (Catd_cat K) E D ≡ Functord_cat E D;
assert [K : Cat] [E D : τ (Catd K)] (FF GG : τ (Functord E D)) ⊢
  Hom_cat (Functord_cat E D) FF GG ≡ Transfd_cat FF GG;

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

symbol Transf_cat : Π [A B : Cat], Π (F G : τ (Functor A B)), Cat;

symbol Transf [A B : Cat] (F G : τ (Functor A B)) : Grpd
≔ Obj (@Transf_cat A B F G);

// Controlled Obj-inversion for transformation categories. This is the
// emdash2 helper that lets projection rules keep source/target functors
// implicit, e.g. `@tapp0_fapp0 ... _ _ ...`, without forcing reducible
// compound family expressions into rewrite-rule LHSs.
unif_rule Obj (@Transf_cat $A $B $F $G) ≡ Obj (@Transf_cat $A' $B' $F' $G')
  ↪ [ $A ≡ $A'; $B ≡ $B'; $F ≡ $F'; $G ≡ $G' ];
unif_rule Transf $F $G ≡ Transf $F' $G' ↪ [ $F ≡ $F'; $G ≡ $G' ];

rule Hom_cat (Functor_cat _ _) $F $G ↪ Transf_cat $F $G;
rule @Transf_cat $K Cat_cat $E $D ↪ @Functord_cat $K $E $D;

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

rule @tapp0_fapp0 $A $B $F $H $Y (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
  ↪ @comp_fapp0
      $B
      (@fapp0 $A $B $F $Y)
      (@fapp0 $A $B $G $Y)
      (@fapp0 $A $B $H $Y)
      (@tapp0_fapp0 $A $B $G $H $Y $η)
      (@tapp0_fapp0 $A $B $F $G $Y $ϵ);

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
        (@comp_cat_fapp0
          (Op_cat A)
          (Op_cat B)
          (Catd_cat A)
          (@hom_int B A G)
          (@Op_func A B F))));

symbol fapp1_int_transf : Π [A B : Cat], Π (F : τ (Functor A B)),
  τ (Transf
      (@hom_int A A (@id_func A))
      (@comp_cat_fapp0
        (Op_cat A)
        (Op_cat B)
        (Catd_cat A)
        (@hom_int B A F)
        (@Op_func A B F)));

rule fapp0 (@tapp1_int_func_transf $A $B $F $F) (id (Functor_cat $A $B) $F)
  ↪ @fapp1_int_transf $A $B $F;

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  fapp0 (@tapp1_int_func_transf A B F F) (id (Functor_cat A B) F)
    ≡ @fapp1_int_transf A B F;

// -------------------------------------------------------------------------------------------------
// 6. Directed Cat-valued family constructors
// -------------------------------------------------------------------------------------------------

symbol Fibre_cat [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) : Cat
≔ @fapp0 K Cat_cat E k;

// Directed-family inference helper for surface notation `E[x]`.
unif_rule Obj (Fibre_cat $E $k) ≡ Obj (Fibre_cat $E' $k') ↪ [ $E ≡ $E'; $k ≡ $k' ];

symbol Pullback_catd [A B : Cat] (E : τ (Catd B)) (F : τ (Functor A B))
  : τ (Catd A)
≔ @comp_cat_fapp0 A B Cat_cat E F;

symbol Const_catd (K : Cat) (A : Cat) : τ (Catd K);

rule @fapp0 $K Cat_cat (@Const_catd $K $A) $_ ↪ $A;

rule @fapp1_func $K Cat_cat (@Const_catd $K $A) $x $y
  ↪ @Const_func
      (Hom_cat $K $x $y)
      (Functor_cat $A $A)
      (@id_func $A);

rule @fapp1_fapp0 $K Cat_cat (@Const_catd $K $A) $x $y $_ ↪ @id_func $A;

symbol Terminal_catd (K : Cat) : τ (Catd K);

rule @fapp0 $K Cat_cat (@Terminal_catd $K) $_ ↪ Terminal_cat;
rule @fapp1_func $K Cat_cat (@Terminal_catd $K) $x $y
  ↪ @Const_func
      (Hom_cat $K $x $y)
      (Functor_cat Terminal_cat Terminal_cat)
      (@id_func Terminal_cat);
rule @fapp1_fapp0 $K Cat_cat (@Terminal_catd $K) $x $y $_ ↪ @id_func Terminal_cat;

symbol Op_catd [K : Cat] (E : τ (Catd K)) : τ (Catd K);

rule @fapp0 $K Cat_cat (@Op_catd $K $E) $k
  ↪ Op_cat (@fapp0 $K Cat_cat $E $k);

rule @Op_catd $K (@Op_catd $K $E) ↪ $E;
rule @Op_catd $K (@Const_catd $K $A) ↪ @Const_catd $K (Op_cat $A);
rule @Op_catd $K (@Terminal_catd $K) ↪ @Terminal_catd $K;

symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat;

rule @Transf_cat $K Cat_cat (@Terminal_catd $K) $E ↪ @Pi_cat $K $E;
rule @Functord_cat $K (@Terminal_catd $K) $E ↪ @Pi_cat $K $E;
rule @Pi_cat $K (@Const_catd $K $A) ↪ Functor_cat $K $A;

unif_rule @Pi_cat $K $E ≡ @Pi_cat $K' $E' ↪ [ $K ≡ $K'; $E ≡ $E' ];
unif_rule Obj (@Pi_cat $K $E) ≡ Obj (@Pi_cat $K' $E') ↪ [ $K ≡ $K'; $E ≡ $E' ];

symbol Pi_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
rule @fapp0 (@Catd_cat $K) Cat_cat (@Pi_func $K) $E
  ↪ @Pi_cat $K $E;

symbol piapp0 : Π [K : Cat], Π [E : τ (Catd K)],
  Π (s : τ (Obj (Pi_cat E))),
  Π (k : τ (Obj K)),
  τ (Obj (Fibre_cat E k));

// Stable head for applying a directed family along a base arrow.
// These identity/composition rules are operational stable-head laws for
// Cat-valued functor action. Semantically they are consequences of ordinary
// functoriality; the skeleton keeps them explicit until generic functor laws
// are represented as rewrite-normal forms.
sequential symbol fib_cov_tapp0_fapp0 : Π [K : Cat] (E : τ (Catd K)),
  Π [x y : τ (Obj K)], Π (f : τ (Hom K x y)),
  Π (u : τ (Obj (Fibre_cat E x))),
  τ (Obj (Fibre_cat E y));

rule fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $f) $u
  ↪ @fib_cov_tapp0_fapp0 $K $E $x $y $f $u;

rule @fib_cov_tapp0_fapp0 $K $E $x $x (id $K $x) $u ↪ $u;
rule @fib_cov_tapp0_fapp0 $K $E $y $z $g (@fib_cov_tapp0_fapp0 $K $E $x $y $f $u)
  ↪ @fib_cov_tapp0_fapp0 $K $E $x $z (comp_fapp0 $g $f) $u;

// -------------------------------------------------------------------------------------------------
// 7. Directed Sigma categories and maps between totals
// -------------------------------------------------------------------------------------------------

symbol Sigma_cat [K : Cat] (E : τ (Catd K)) : Cat;

symbol Sigma_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
rule @fapp0 (@Catd_cat $K) Cat_cat (@Sigma_func $K) $E
  ↪ @Sigma_cat $K $E;

rule τ (Obj (@Sigma_cat $K $E))
  ↪ `τΣ_ k : τ (Obj $K), Obj (Fibre_cat $E k);

injective symbol Sigma_proj1_func [K : Cat] (E : τ (Catd K))
  : τ (Functor (Sigma_cat E) K);

rule fapp0 (Sigma_proj1_func $E) (Struct_sigma $k $u) ↪ $k;

symbol sigma_map_func [K : Cat] [E D : τ (Catd K)]
  (η : τ (Functord E D))
  : τ (Functor (Sigma_cat E) (Sigma_cat D));

rule @fapp1_fapp0 (@Catd_cat $K) Cat_cat (@Sigma_func $K) $E $D $η
  ↪ @sigma_map_func $K $E $D $η;

rule @fapp0 _ _
      (@sigma_map_func $K $E $D $η)
      (Struct_sigma $k $u)
  ↪ @Struct_sigma
      (Obj $K)
      (λ kk : τ (Obj $K), Obj (Fibre_cat $D kk))
      $k
      (@fapp0 (Fibre_cat $E $k) (Fibre_cat $D $k)
        (@tapp0_fapp0 $K Cat_cat $E $D $k $η) $u);

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
≔ @comp_cat_fapp0
     (Op_cat Z)
     (Functor_cat Z Cat_cat)
     (Functor_cat Z Cat_cat)
     (@op_val_func Z)
     (@hom_int Z Z (@id_func Z));

symbol Presheaf_catd_func (K : Cat)
  : τ (Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Catd_cat K))
≔ @comp_cat_fapp0
     (Op_cat (Catd_cat (Op_cat K)))
     (Functor_cat (Catd_cat K) (Catd_cat K))
     (Catd_cat K)
     (@fapp0_func (Catd_cat K) (Catd_cat K) (@Const_catd K Cat_cat))
     (@Functor_catd_mix_func K);

symbol HomPresheaf_catd [Z : Cat]
  : τ (Functor Z (Catd_cat (Op_cat Z)))
≔ @comp_cat_fapp0
     Z
     (Op_cat (Catd_cat Z))
     (Catd_cat (Op_cat Z))
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

constant symbol homd_int : Π [Z : Cat], Π (E : τ (Catd Z)), τ (Homd E);

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

// Semantic endpoint used by the primitive `homd_` action rules. This is kept
// off rewrite LHSs; it records the former definitional sigma-hom endpoint.
symbol homd_semantic_func [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat)
≔ @hom_con
     (Fibre_cat E y)
     v
     (Hom_cat Z x y)
     (@fib_cov_tapp0_func Z E x y u);

// Component functor after projecting the fully internal homd object at x.
symbol homd_src_func [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  : τ (Functor
        (Fibre_cat (@Homd_source_catd Z E) x)
        (Pi_cat (@Homd_section_catd Z E x)));

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
      (@homd_int $Z $E)
  ↪ @homd_src_func $Z $E $x;

// Source-fixed projection after evaluating the component functor at u.
symbol homd_src_sec [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (@Homd_section_catd Z E x)));

// Second projection fold: externalize x,u and keep the y,v endpoint internal.
rule fapp0 (@homd_src_func $Z $E $x) $u
  ↪ @homd_src_sec $Z $E $x $u;

// Endpoint normal form. This is a stable head whose object-action is the
// former sigma-hom formula. Keeping the head visible lets constant/terminal
// family cases normalize before pointwise evaluation.
symbol homd_ [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat);

rule @fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat (@homd_ $K $E $x $u $y $v) $f
  ↪ Hom_cat
      (Fibre_cat $E $y)
      (@fib_cov_tapp0_fapp0 $K $E $x $y $f $u)
      $v;

// The source category is explicit here, as in the object-action rule above:
// Lambdapi needs it for subject reduction, and it is the stable Op/Hom spine,
// not a defined family alias.
rule @fapp1_func _ Cat_cat (@homd_ $K $E $x $u $y $v) $f $g
  ↪ @fapp1_func
      (Op_cat (Hom_cat $K $x $y))
      Cat_cat
      (@homd_semantic_func $K $E $x $u $y $v)
      $f
      $g;

rule @fapp1_fapp0 _ Cat_cat (@homd_ $K $E $x $u $y $v) $f $g $alpha
  ↪ @fapp1_fapp0
      (Op_cat (Hom_cat $K $x $y))
      Cat_cat
      (@homd_semantic_func $K $E $x $u $y $v)
      $f
      $g
      $alpha;

rule @homd_ $K (@Const_catd $K $A) $x $u $y $v
  ↪ @Const_catd (Op_cat (Hom_cat $K $x $y)) (Hom_cat $A $u $v);

rule @homd_ $K (@Terminal_catd $K) $x $_ $y $_
  ↪ @Terminal_catd (Op_cat (Hom_cat $K $x $y));

// Inner endpoint functor after projecting the source-fixed section at y.
symbol homd_tgt_func [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  : τ (Functor
        (Fibre_cat E y)
        (Fibre_cat
          (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd Z) x)
          y));

// Third projection fold. The family argument of `piapp0` is intentionally
// implicit: its normal form is a mixed-variance `Functor_catd` involving
// `HomPresheaf_catd`, and spelling that compound in the LHS makes matching
// brittle. The base is kept explicit because it is a stable `Op_cat` head and
// is needed for subject reduction.
rule @piapp0
      _
      _
      (@homd_src_sec $Z $E $x $u)
      $y
  ↪ @homd_tgt_func $Z $E $x $u $y;

// Final endpoint fold. At this point the stable head `homd_` carries the
// endpoint family; pointwise object-action is handled by the rule on `homd_`.
rule fapp0 (@homd_tgt_func $Z $E $x $u $y) $v
  ↪ @homd_ $Z $E $x $u $y $v;

rule Hom_cat (@Sigma_cat $K $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_cat
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (@homd_ $K $E $x $u $y $v));

// -------------------------------------------------------------------------------------------------
// 12. Generic Sigma/Pi weakening helpers
// -------------------------------------------------------------------------------------------------

// TODO(v3.1): generic Sigma/Pi helpers are deferred until the
// directed-family core is stable enough for robust beta assertions. See the
// backlog in reports/REPORT_EMDASH_V3_CONSOLIDATED.md.

// -------------------------------------------------------------------------------------------------
// 13. Regression assertions for the mixed-variance skeleton
// -------------------------------------------------------------------------------------------------

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  Fibre_cat E k ≡ @fapp0 K Cat_cat E k;

assert [K : Cat] (A : Cat) (k : τ (Obj K)) ⊢
  Fibre_cat (Const_catd K A) k ≡ A;

assert [K : Cat] (k : τ (Obj K)) ⊢
  Fibre_cat (Terminal_catd K) k ≡ Terminal_cat;

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

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Pi_func K) E ≡ Pi_cat E;

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
    (@homd_int Z E)
    ≡ @homd_src_func Z E x;

assert [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@homd_src_func Z E x) u
    ≡ @homd_src_sec Z E x u;

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
    ≡ @homd_ Z E x u y v;

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y))) ⊢
  @homd_ K (Const_catd K A) x u y v
    ≡ @Const_catd (Op_cat (Hom_cat K x y)) (Hom_cat A u v);

assert [K : Cat] (A : Cat)
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Const_catd K A) x)))
  (v : τ (Obj (Fibre_cat (Const_catd K A) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K (Const_catd K A) x u y v)
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
    (@homd_ K (Const_catd K A) x u y v)
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
  @homd_ K (Terminal_catd K) x u y v
    ≡ @Terminal_catd (Op_cat (Hom_cat K x y));

assert [K : Cat]
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat (Terminal_catd K) x)))
  (v : τ (Obj (Fibre_cat (Terminal_catd K) y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K (Terminal_catd K) x u y v)
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
    (@homd_ K (Terminal_catd K) x u y v)
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

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_semantic_func K E x u y v)
    f
    ≡ Hom_cat (Fibre_cat E y)
        (@fib_cov_tapp0_fapp0 K E x y f u)
        v;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_ K E x u y v)
    f
    ≡ Hom_cat (Fibre_cat E y)
        (@fib_cov_tapp0_fapp0 K E x y f u)
        v;

assert [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (f g : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp1_func
    (Op_cat (Hom_cat K x y))
    Cat_cat
    (@homd_ K E x u y v)
    f
    g
    ≡ @fapp1_func
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@homd_semantic_func K E x u y v)
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
    (@homd_ K E x u y v)
    f
    g
    alpha
    ≡ @fapp1_fapp0
        (Op_cat (Hom_cat K x y))
        Cat_cat
        (@homd_semantic_func K E x u y v)
        f
        g
        alpha;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  Hom_cat (@Sigma_cat Z E) (Struct_sigma x u) (Struct_sigma y v)
    ≡ Op_cat
        (@Sigma_cat
          (Op_cat (Hom_cat Z x y))
          (@homd_ Z E x u y v));

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

/*
  Deferred with the helper declarations above:

  - sigma_intro_transf beta
  - pi_eval_transf beta
  - const_section_func beta
  - section_pullback_func beta
*/
