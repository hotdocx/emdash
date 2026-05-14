/*
  m- / emdash3.1
  Directed-family mixed-variance implementation draft.

  This file starts the architecture described in
  reports/emdash3_mix_variance_architecture.md.  It reuses the stable
  category/universe/internal-hom prefix from emdash3.lp, but replaces the
  Catd foundation with directed Cat-valued families:

    Fam_cat K := Functor_cat K Cat_cat.
*/

flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;

/*
  Ported working conventions from emdash2.lp

  Surface reading for this directed-family draft:
    - `E[x]` means `Fam_app_cat E x`, for `E : Fam Z`.
    - `F[x]` means `fapp0 F x`, for an ordinary functor.
    - `ϵ[x]` means the diagonal component extracted by `tapp0_fapp0 x ϵ`.
    - `homd_int E`, after projection at x,u,y,v, normalizes through
      `homd_src_func`, `homd_src_sec`, `homd_tgt_func`, then the endpoint `homd_`.

  Rewrite hygiene:
    - Keep inferred/implicit arguments on rule LHSs as `_` unless they are
      essential discriminators.
    - This matters most when an implicit argument would be a reducible compound
      term, such as a family built from `Functor_fam`, `HomPresheaf_fam`, or
      `comp_cat_fapp0`.
    - Prefer small projection rules with stable heads over a single large nested
      redex.  The homd endpoint is deliberately split into `tapp0_fapp0`,
      `fapp0`, `piapp0`, and `fapp0` folds for this reason.

  Normalization policy:
    - Introduce stable heads for functor-level data that later rules need to
      recognize (`comp_cat_fapp0`, `fib_cov_tapp0_fapp0`, `homd_src_func`,
      `homd_src_sec`, `homd_tgt_func`).
    - The final endpoint `homd_` is not an independent opaque table of beta
      rules: it is the old `sigma_hom_fam` formula
      `hom_con v (fam_tapp0_func E x y u)`.
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

constant symbol Functor_cat : Π (A B : Cat), Cat;

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

// Internalized opposite as a functor in Cat: A |-> A^op.
constant symbol op : τ (Functor Cat_cat Cat_cat);
rule @fapp0 _ _ op $A ↪ Op_cat $A;
rule @fapp1_fapp0 Cat_cat Cat_cat op $A $B $F ↪ @Op_func $A $B $F;

// Internalized ordinary functor-category formation.
symbol Functor_cat_func : τ (Functor (Op_cat Cat_cat) (Functor_cat Cat_cat Cat_cat));

symbol Functor_cat_fapp0_func (A : Cat) : τ (Functor Cat_cat Cat_cat);

rule fapp0 Functor_cat_func $A ↪ Functor_cat_fapp0_func $A;
rule fapp0 (Functor_cat_fapp0_func $A) $B ↪ Functor_cat $A $B;

// Curried postcomposition in Cat, used to build constructor pipelines.
symbol comp_cat_cov_func : Π [X Y Z : Cat],
  Π (G : τ (Functor Y Z)),
  τ (Functor (Functor_cat X Y) (Functor_cat X Z));

rule fapp0 (@comp_cat_cov_func $X $Y $Z $G) $F
  ↪ comp_cat_fapp0 $G $F;

symbol op_val_func [Z : Cat] : τ (Functor (Functor_cat Z Cat_cat) (Functor_cat Z Cat_cat))
≔ @comp_cat_cov_func Z Cat_cat Cat_cat op;

// -------------------------------------------------------------------------------------------------
// 3. Curried internal hom
// -------------------------------------------------------------------------------------------------

symbol hom_ [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  : τ (Functor B Cat_cat);
rule @fapp0 $B Cat_cat (@hom_ $A $B $F $W) $y
  ↪ Hom_cat $A $W (@fapp0 $B $A $F $y);

symbol hom_con [A : Cat] (W : τ (Obj A)) [B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat B) Cat_cat);
rule @hom_con $A $W $B $F
  ↪ @hom_ (Op_cat $A) (Op_cat $B) (@Op_func $B $A $F) $W;

symbol hom_int [A B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat A) (Functor_cat B Cat_cat));

rule @fapp0 (Op_cat $A) (Functor_cat $B Cat_cat) (@hom_int $A $B $F) $W
  ↪ @hom_ $A $B $F $W;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (y : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@hom_ A B F W) y ≡ Hom_cat A W (@fapp0 B A F y);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (x : τ (Obj (Op_cat B))) ⊢
  @fapp0 (Op_cat B) Cat_cat (@hom_con A W B F) x ≡ Hom_cat A (@fapp0 B A F x) W;

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj (Op_cat A))) ⊢
  @fapp0 (Op_cat A) (Functor_cat B Cat_cat) (@hom_int A B F) W
    ≡ @hom_ A B F W;

assert [A B : Cat] (F : τ (Functor B A)) (X : τ (Obj (Op_cat A))) (Y : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@fapp0 (Op_cat A) (Functor_cat B Cat_cat) (@hom_int A B F) X) Y
    ≡ Hom_cat A X (fapp0 F Y);

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

constant symbol Transf_cat : Π [A B : Cat], Π (F G : τ (Functor A B)), Cat;

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

// -------------------------------------------------------------------------------------------------
// 6. Directed Cat-valued families
// -------------------------------------------------------------------------------------------------

symbol Fam_cat (K : Cat) : Cat
≔ Functor_cat K Cat_cat;

symbol Fam (K : Cat) : Grpd
≔ Obj (Fam_cat K);

symbol Fam_app_cat [K : Cat] (E : τ (Fam K)) (k : τ (Obj K)) : Cat
≔ @fapp0 K Cat_cat E k;

// Directed-family inference helpers. As above, these are elaboration aids for
// the surface reading `E[x]`; they are not a claim that every abbreviation
// around `Fam_cat` should be globally injective.
unif_rule Fam $K ≡ Fam $K' ↪ [ $K ≡ $K' ];
unif_rule Obj (Fam_app_cat $E $k) ≡ Obj (Fam_app_cat $E' $k') ↪ [ $E ≡ $E'; $k ≡ $k' ];

symbol Pullback_fam [A B : Cat] (E : τ (Fam B)) (F : τ (Functor A B))
  : τ (Fam A)
≔ @comp_cat_fapp0 A B Cat_cat E F;

symbol Const_fam (K : Cat) (A : Cat) : τ (Fam K)
≔ @comp_cat_fapp0 K Terminal_cat Cat_cat (@Obj_func Cat_cat A) (@Terminal_func K);

symbol Terminal_fam (K : Cat) : τ (Fam K)
≔ Const_fam K Terminal_cat;

symbol Pi_cat [K : Cat] (E : τ (Fam K)) : Cat
≔ @Transf_cat K Cat_cat (@Terminal_fam K) E;

symbol Pi_func (K : Cat) : τ (Functor (Fam_cat K) Cat_cat);
rule fapp0 (@Pi_func $K) $E ↪ @Pi_cat $K $E;

symbol piapp0 : Π [K : Cat], Π [E : τ (Fam K)],
  Π (s : τ (Obj (Pi_cat E))),
  Π (k : τ (Obj K)),
  τ (Obj (Fam_app_cat E k));

// Stable head for applying a directed family along a base arrow.
// These identity/composition rules are operational stable-head laws for
// Cat-valued functor action. Semantically they are consequences of ordinary
// functoriality; the skeleton keeps them explicit until generic functor laws
// are represented as rewrite-normal forms.
sequential symbol fib_cov_tapp0_fapp0 : Π [K : Cat] (E : τ (Fam K)),
  Π [x y : τ (Obj K)], Π (f : τ (Hom K x y)),
  Π (u : τ (Obj (Fam_app_cat E x))),
  τ (Obj (Fam_app_cat E y));

rule fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $f) $u
  ↪ @fib_cov_tapp0_fapp0 $K $E $x $y $f $u;

rule @fib_cov_tapp0_fapp0 $K $E $x $x (id $K $x) $u ↪ $u;
rule @fib_cov_tapp0_fapp0 $K $E $y $z $g (@fib_cov_tapp0_fapp0 $K $E $x $y $f $u)
  ↪ @fib_cov_tapp0_fapp0 $K $E $x $z (comp_fapp0 $g $f) $u;

// -------------------------------------------------------------------------------------------------
// 7. Directed Sigma categories and maps between totals
// -------------------------------------------------------------------------------------------------

symbol Sigma_cat [K : Cat] (E : τ (Fam K)) : Cat;

symbol Sigma_func (K : Cat) : τ (Functor (Fam_cat K) Cat_cat);
rule fapp0 (@Sigma_func $K) $E ↪ @Sigma_cat $K $E;

rule τ (Obj (@Sigma_cat $K $E))
  ↪ `τΣ_ k : τ (Obj $K), Obj (Fam_app_cat $E k);

injective symbol Sigma_proj1_func [K : Cat] (E : τ (Fam K))
  : τ (Functor (Sigma_cat E) K);

rule fapp0 (Sigma_proj1_func $E) (Struct_sigma $k $u) ↪ $k;

symbol sigma_map_func [K : Cat] [E D : τ (Fam K)]
  (η : τ (Obj (Transf_cat E D)))
  : τ (Functor (Sigma_cat E) (Sigma_cat D));

rule @fapp1_fapp0 (Functor_cat $K Cat_cat) Cat_cat (@Sigma_func $K) $E $D $η
  ↪ @sigma_map_func $K $E $D $η;

rule @fapp0 (@Sigma_cat $K $E) (@Sigma_cat $K $D)
      (@sigma_map_func $K $E $D $η)
      (Struct_sigma $k $u)
  ↪ @Struct_sigma
      (Obj $K)
      (λ kk : τ (Obj $K), Obj (Fam_app_cat $D kk))
      $k
      (@fapp0 (Fam_app_cat $E $k) (Fam_app_cat $D $k)
        (@tapp0_fapp0 $K Cat_cat $E $D $k $η) $u);

rule @comp_cat_fapp0 (@Sigma_cat $K $E) (@Sigma_cat $K $D) $K
      (@Sigma_proj1_func $K $D)
      (@sigma_map_func $K $E $D $η)
  ↪ @Sigma_proj1_func $K $E;

// -------------------------------------------------------------------------------------------------
// 8. Mixed-variance family functor
// -------------------------------------------------------------------------------------------------

symbol Functor_fam [K : Cat]
  (A : τ (Fam (Op_cat K)))
  (B : τ (Fam K))
  : τ (Fam K);

rule @fapp0 $K Cat_cat (@Functor_fam $K $A $B) $k
  ↪ Functor_cat (Fam_app_cat $A $k) (Fam_app_cat $B $k);

symbol Functor_mix_fam_func (K : Cat)
  : τ (Functor
      (Op_cat (Fam_cat (Op_cat K)))
      (Functor_cat (Fam_cat K) (Fam_cat K)));

symbol Functor_mix_fam_fapp0_func [K : Cat]
  (A : τ (Fam (Op_cat K)))
  : τ (Functor (Fam_cat K) (Fam_cat K));

rule fapp0 (@Functor_mix_fam_func $K) $A
  ↪ @Functor_mix_fam_fapp0_func $K $A;

rule fapp0 (@Functor_mix_fam_fapp0_func $K $A) $B
  ↪ @Functor_fam $K $A $B;

// -------------------------------------------------------------------------------------------------
// 9. Internal edge and presheaf-family classifiers
// -------------------------------------------------------------------------------------------------

symbol Edge_fam [Z : Cat]
  : τ (Functor (Op_cat Z) (Fam_cat Z))
≔ @comp_cat_fapp0
     (Op_cat Z)
     (Functor_cat Z Cat_cat)
     (Functor_cat Z Cat_cat)
     (@op_val_func Z)
     (@hom_int Z Z (@id_func Z));

symbol Presheaf_fam_func (K : Cat)
  : τ (Functor
      (Op_cat (Fam_cat (Op_cat K)))
      (Fam_cat K))
≔ @comp_cat_fapp0
     (Op_cat (Fam_cat (Op_cat K)))
     (Functor_cat (Fam_cat K) (Fam_cat K))
     (Fam_cat K)
     (@fapp0_func (Fam_cat K) (Fam_cat K) (@Const_fam K Cat_cat))
     (@Functor_mix_fam_func K);

symbol HomPresheaf_fam [Z : Cat]
  : τ (Functor Z (Fam_cat (Op_cat Z)))
≔ @comp_cat_fapp0
     Z
     (Op_cat (Fam_cat Z))
     (Fam_cat (Op_cat Z))
     (@Presheaf_fam_func (Op_cat Z))
     (@Op_func (Op_cat Z) (Fam_cat Z) (@Edge_fam Z));

// -------------------------------------------------------------------------------------------------
// 10. Directed homd target and internal homd category
// -------------------------------------------------------------------------------------------------

/*
  Homd architecture note:
  `Homd_source_fam`, `Homd_section_fam`, and `Homd_target_fam` name the
  intended source/target families for readability and assertions.  They are
  not used as required discriminants in the projection-rule LHSs below, because
  those positions are inferred implicit arguments and may reduce to canonical
  compound terms before matching.
*/

symbol Homd_source_fam [Z : Cat] (E : τ (Fam Z))
  : τ (Fam Z)
≔ @fapp0
     (Functor_cat Z Cat_cat)
     (Functor_cat Z Cat_cat)
     (@op_val_func Z)
     E;

symbol Homd_section_fam [Z : Cat] (E : τ (Fam Z))
  (x : τ (Obj Z))
  : τ (Fam (Op_cat Z))
≔ @Functor_fam
     (Op_cat Z)
     E
     (@fapp0 Z (Fam_cat (Op_cat Z)) (@HomPresheaf_fam Z) x);

symbol Homd_target_fam [Z : Cat] (E : τ (Fam Z))
  : τ (Fam Z)
≔ @comp_cat_fapp0
     Z
     (Fam_cat (Op_cat Z))
     Cat_cat
     (@comp_cat_fapp0
       (Fam_cat (Op_cat Z))
       (Fam_cat (Op_cat Z))
       Cat_cat
       (@Pi_func (Op_cat Z))
       (@fapp0
         (Op_cat (Fam_cat Z))
         (Functor_cat (Fam_cat (Op_cat Z)) (Fam_cat (Op_cat Z)))
         (@Functor_mix_fam_func (Op_cat Z))
         E))
     (@HomPresheaf_fam Z);

symbol Homd_cat [Z : Cat] (E : τ (Fam Z)) : Cat
≔ @Transf_cat Z Cat_cat (@Homd_source_fam Z E) (@Homd_target_fam Z E);

symbol Homd [Z : Cat] (E : τ (Fam Z)) : Grpd
≔ Obj (@Homd_cat Z E);

constant symbol homd_int : Π [Z : Cat], Π (E : τ (Fam Z)), τ (Homd E);

// -------------------------------------------------------------------------------------------------
// 11. Endpoint normal forms for Sigma homs
// -------------------------------------------------------------------------------------------------

symbol fam_tapp0_func [K : Cat] (E : τ (Fam K))
  [x y : τ (Obj K)]
  (u : τ (Obj (Fam_app_cat E x)))
  : τ (Functor (Hom_cat K x y) (Fam_app_cat E y))
≔ @comp_cat_fapp0
     (Hom_cat K x y)
     (Functor_cat (Fam_app_cat E x) (Fam_app_cat E y))
     (Fam_app_cat E y)
     (@fapp0_func (Fam_app_cat E x) (Fam_app_cat E y) u)
     (@fapp1_func K Cat_cat E x y);

// Component functor after projecting the fully internal homd object at x.
symbol homd_src_func [Z : Cat] (E : τ (Fam Z))
  (x : τ (Obj Z))
  : τ (Functor
        (Fam_app_cat (@Homd_source_fam Z E) x)
        (Pi_cat (@Homd_section_fam Z E x)));

// First projection fold. The source and target family arguments are
// deliberately `_`: their canonical forms contain reducible expressions such
// as `fapp0 (op_val_func Z) E` and `Homd_target_fam E`.  The Transf_cat
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
symbol homd_src_sec [Z : Cat] (E : τ (Fam Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fam_app_cat E x)))
  : τ (Obj (Pi_cat (@Homd_section_fam Z E x)));

// Second projection fold: externalize x,u and keep the y,v endpoint internal.
rule fapp0 (@homd_src_func $Z $E $x) $u
  ↪ @homd_src_sec $Z $E $x $u;

// Endpoint normal form. This is intentionally the old sigma_hom_fam
// definition, not an independent head with its own object-action rule.
symbol homd_ [Z : Cat] (E : τ (Fam Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fam_app_cat E x)))
  (y : τ (Obj Z))
  (v : τ (Obj (Fam_app_cat E y)))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat)
≔ @hom_con
     (Fam_app_cat E y)
     v
     (Hom_cat Z x y)
     (@fam_tapp0_func Z E x y u);

// Inner endpoint functor after projecting the source-fixed section at y.
symbol homd_tgt_func [Z : Cat] (E : τ (Fam Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fam_app_cat E x)))
  (y : τ (Obj Z))
  : τ (Functor
        (Fam_app_cat E y)
        (Fam_app_cat
          (@fapp0 Z (Fam_cat (Op_cat Z)) (@HomPresheaf_fam Z) x)
          y));

// Third projection fold. The family argument of `piapp0` is intentionally
// implicit: its normal form is a mixed-variance `Functor_fam` involving
// `HomPresheaf_fam`, and spelling that compound in the LHS makes matching
// brittle.
rule @piapp0
      (Op_cat $Z)
      _
      (@homd_src_sec $Z $E $x $u)
      $y
  ↪ @homd_tgt_func $Z $E $x $u $y;

// Final endpoint fold. At this point the stable head `homd_` is definitionally
// the sigma-hom family formula, so no separate object-action shortcut is used.
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

/*
  TODO(v3.1): these helpers are planned generic infrastructure. Their
  declarations and beta rules are syntactically plausible, but the intended
  beta assertions did not validate as stable rewrite normal forms in the first
  pass. They are optional for the mixed-variance Homd target below, so they
  stay deferred until the canonical directed-family core is stable.

symbol sigma_intro_transf [K : Cat] (E : τ (Fam K))
  : τ (Obj (@Transf_cat K Cat_cat E (@Const_fam K (@Sigma_cat K E))));

rule @fapp0 (Fam_app_cat $E $k) (Fam_app_cat (@Const_fam $K (@Sigma_cat $K $E)) $k)
      (@tapp0_fapp0 $K Cat_cat $E (@Const_fam $K (@Sigma_cat $K $E)) $k (@sigma_intro_transf $K $E))
      $u
  ↪ @Struct_sigma
      (Obj $K)
      (λ kk : τ (Obj $K), Obj (Fam_app_cat $E kk))
      $k
      $u;

symbol pi_eval_transf [K : Cat] (E : τ (Fam K))
  : τ (Obj (@Transf_cat K Cat_cat (@Const_fam K (@Pi_cat K E)) E));

rule @fapp0 (Fam_app_cat (@Const_fam $K (@Pi_cat $K $E)) $k) (Fam_app_cat $E $k)
      (@tapp0_fapp0 $K Cat_cat (@Const_fam $K (@Pi_cat $K $E)) $E $k (@pi_eval_transf $K $E))
      $s
  ↪ @piapp0 $K $E $s $k;

symbol const_section_func (K : Cat) (A : Cat)
  : τ (Functor A (@Pi_cat K (@Const_fam K A)));

rule @piapp0 $K (@Const_fam $K $A)
      (@fapp0 $A (@Pi_cat $K (@Const_fam $K $A)) (@const_section_func $K $A) $a)
      $k
  ↪ $a;

symbol section_pullback_func [A B : Cat]
  (F : τ (Functor A B))
  (E : τ (Fam B))
  : τ (Functor (@Pi_cat B E) (@Pi_cat A (@Pullback_fam A B E F)));

rule @piapp0 $A (@Pullback_fam $A $B $E $F)
      (@fapp0 (@Pi_cat $B $E) (@Pi_cat $A (@Pullback_fam $A $B $E $F))
        (@section_pullback_func $A $B $F $E) $s)
      $a
  ↪ @piapp0 $B $E $s (@fapp0 $A $B $F $a);
*/

// -------------------------------------------------------------------------------------------------
// 13. Regression assertions for the mixed-variance skeleton
// -------------------------------------------------------------------------------------------------

assert [K : Cat] (E : τ (Fam K)) (k : τ (Obj K)) ⊢
  Fam_app_cat E k ≡ fapp0 E k;

assert [K : Cat] (A : Cat) (k : τ (Obj K)) ⊢
  Fam_app_cat (Const_fam K A) k ≡ A;

assert [A B : Cat] (E : τ (Fam B)) (F : τ (Functor A B)) (a : τ (Obj A)) ⊢
  Fam_app_cat (Pullback_fam E F) a ≡ Fam_app_cat E (fapp0 F a);

assert [K : Cat] (E : τ (Fam K)) ⊢
  fapp0 (Pi_func K) E ≡ Pi_cat E;

assert [K : Cat] (E : τ (Fam K)) ⊢
  fapp0 (Sigma_func K) E ≡ Sigma_cat E;

assert [K : Cat] (E D : τ (Fam K)) (η : τ (Obj (Transf_cat E D))) ⊢
  @fapp1_fapp0 (Fam_cat K) Cat_cat (@Sigma_func K) E D η
    ≡ @sigma_map_func K E D η;

assert [K : Cat] (E : τ (Fam K)) (k : τ (Obj K)) (u : τ (Obj (Fam_app_cat E k))) ⊢
  fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ≡ k;

assert [K : Cat] (A : τ (Fam (Op_cat K))) (B : τ (Fam K)) (k : τ (Obj K)) ⊢
  Fam_app_cat (Functor_fam A B) k
    ≡ Functor_cat (Fam_app_cat A k) (Fam_app_cat B k);

assert [K : Cat] (A : τ (Fam (Op_cat K))) (B : τ (Fam K)) ⊢
  @fapp0 (Fam_cat K) (Fam_cat K)
    (@fapp0
      (Op_cat (Fam_cat (Op_cat K)))
      (Functor_cat (Fam_cat K) (Fam_cat K))
      (@Functor_mix_fam_func K)
      A)
    B
    ≡ Functor_fam A B;

assert [Z : Cat] (x : τ (Obj (Op_cat Z))) (y : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat
    (@fapp0 (Op_cat Z) (Fam_cat Z) (@Edge_fam Z) x)
    y
    ≡ Op_cat (Hom_cat Z x y);

assert [Z : Cat] (x : τ (Obj Z)) (y : τ (Obj (Op_cat Z))) ⊢
  Fam_app_cat (@fapp0 Z (Fam_cat (Op_cat Z)) (@HomPresheaf_fam Z) x) y
    ≡ Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat;

assert [Z : Cat] (E : τ (Fam Z)) ⊢
  @Homd_source_fam Z E
    ≡ @fapp0
        (Functor_cat Z Cat_cat)
        (Functor_cat Z Cat_cat)
        (@op_val_func Z)
        E;

assert [Z : Cat] (E : τ (Fam Z)) (x : τ (Obj Z)) ⊢
  @Homd_section_fam Z E x
    ≡ @Functor_fam
        (Op_cat Z)
        E
        (@fapp0 Z (Fam_cat (Op_cat Z)) (@HomPresheaf_fam Z) x);

assert [Z : Cat] (E : τ (Fam Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_fam Z E) x
    ≡ Pi_cat
        (Functor_fam
          E
          (@fapp0 Z (Fam_cat (Op_cat Z)) (@HomPresheaf_fam Z) x));

assert [Z : Cat] (E : τ (Fam Z)) (x : τ (Obj Z)) ⊢
  @fapp0 Z Cat_cat (@Homd_target_fam Z E) x
    ≡ Pi_cat (@Homd_section_fam Z E x);

assert [Z : Cat] (E : τ (Fam Z)) ⊢
  @Homd_cat Z E
    ≡ @Transf_cat Z Cat_cat (@comp_cat_fapp0 Z Cat_cat Cat_cat op E) (@Homd_target_fam Z E);

assert [Z : Cat] (E : τ (Fam Z))
  (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (fapp0 (@op_val_func Z) E)
    (@Homd_target_fam Z E)
    x
    (@homd_int Z E)
    ≡ @homd_src_func Z E x;

assert [Z : Cat] (E : τ (Fam Z))
  (x : τ (Obj Z))
  (u : τ (Obj (Fam_app_cat E x))) ⊢
  fapp0 (@homd_src_func Z E x) u
    ≡ @homd_src_sec Z E x u;

assert [Z : Cat] (E : τ (Fam Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fam_app_cat E x))) ⊢
  @piapp0
    (Op_cat Z)
    (@Functor_fam
      (Op_cat Z)
      E
      (fapp0 (@HomPresheaf_fam Z) x))
    (@homd_src_sec Z E x u)
    y
    ≡ @homd_tgt_func Z E x u y;

assert [Z : Cat] (E : τ (Fam Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fam_app_cat E x)))
  (v : τ (Obj (Fam_app_cat E y))) ⊢
  fapp0 (@homd_tgt_func Z E x u y) v
    ≡ @homd_ Z E x u y v;

assert [K : Cat] (E : τ (Fam K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fam_app_cat E x)))
  (f : τ (Hom K x y)) ⊢
  @fapp0 (Hom_cat K x y) (Fam_app_cat E y)
    (@fam_tapp0_func K E x y u)
    f
    ≡ @fib_cov_tapp0_fapp0 K E x y f u;

assert [K : Cat] (E : τ (Fam K))
  (x y : τ (Obj K))
  (u : τ (Obj (Fam_app_cat E x)))
  (v : τ (Obj (Fam_app_cat E y)))
  (f : τ (Obj (Op_cat (Hom_cat K x y)))) ⊢
  @fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_ K E x u y v)
    f
    ≡ Hom_cat (Fam_app_cat E y)
        (@fib_cov_tapp0_fapp0 K E x y f u)
        v;

assert [Z : Cat] (E : τ (Fam Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fam_app_cat E x)))
  (v : τ (Obj (Fam_app_cat E y))) ⊢
  Hom_cat (@Sigma_cat Z E) (Struct_sigma x u) (Struct_sigma y v)
    ≡ Op_cat
        (@Sigma_cat
          (Op_cat (Hom_cat Z x y))
          (@homd_ Z E x u y v));

assert [K : Cat] (E D : τ (Fam K)) (η : τ (Obj (Transf_cat E D)))
  (k : τ (Obj K)) (u : τ (Obj (Fam_app_cat E k))) ⊢
  @fapp0 (@Sigma_cat K E) (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma k u)
    ≡ @Struct_sigma
        (Obj K)
        (λ kk : τ (Obj K), Obj (Fam_app_cat D kk))
        k
        (@fapp0 (Fam_app_cat E k) (Fam_app_cat D k)
          (@tapp0_fapp0 K Cat_cat E D k η)
          u);

assert [K : Cat] (E D : τ (Fam K)) (η : τ (Obj (Transf_cat E D))) ⊢
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
