/*
  m- / emdash3
  Clean executable skeleton for computational-logical omega-categories in Lambdapi.

  v3 keeps the v2 stable-head rewrite discipline, but starts from categorical
  Sigma/Pi type formers and a uniform binary internal hom.
*/

flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;

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

// -------------------------------------------------------------------------------------------------
// 3. Uniform binary internal hom
// -------------------------------------------------------------------------------------------------

constant symbol hom2_int : Π [I J A : Cat],
  Π (G : τ (Functor I A)),
  Π (F : τ (Functor J A)),
  τ (Functor (Op_cat I) (Functor_cat J Cat_cat));

rule @fapp0 $J Cat_cat (@fapp0 (Op_cat $I) (Functor_cat $J Cat_cat) (@hom2_int $I $J $A $G $F) $i) $j
  ↪ Hom_cat $A (@fapp0 $I $A $G $i) (@fapp0 $J $A $F $j);

symbol hom_ [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  : τ (Functor B Cat_cat);
rule @fapp0 $B Cat_cat (@hom_ $A $B $F $W) $y
  ↪ Hom_cat $A $W (@fapp0 $B $A $F $y);

symbol hom_con [A : Cat] (W : τ (Obj A)) [B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat B) Cat_cat);
rule @fapp0 (Op_cat $B) Cat_cat (@hom_con $A $W $B $F) $x
  ↪ Hom_cat $A (@fapp0 $B $A $F $x) $W;

assert [I J A : Cat] (G : τ (Functor I A)) (F : τ (Functor J A))
  (i : τ (Obj (Op_cat I))) (j : τ (Obj J)) ⊢
  @fapp0 J Cat_cat (@fapp0 (Op_cat I) (Functor_cat J Cat_cat) (@hom2_int I J A G F) i) j
    ≡ Hom_cat A (@fapp0 I A G i) (@fapp0 J A F j);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (y : τ (Obj B)) ⊢
  @fapp0 B Cat_cat (@hom_ A B F W) y ≡ Hom_cat A W (@fapp0 B A F y);

assert [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A)) (x : τ (Obj (Op_cat B))) ⊢
  @fapp0 (Op_cat B) Cat_cat (@hom_con A W B F) x ≡ Hom_cat A (@fapp0 B A F x) W;

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
// 5. Displayed categories, Pi/Sigma, and displayed functors
// -------------------------------------------------------------------------------------------------

constant symbol Catd : Π (Z : Cat), TYPE;

constant symbol Catd_grpd : Π (Z : Cat), Grpd;
rule τ (Catd_grpd $Z) ↪ Catd $Z;

constant symbol Catd_cat : Π (Z : Cat), Cat;
rule Obj (Catd_cat $Z) ↪ Catd_grpd $Z;

injective symbol Fibre_cat : Π [Z : Cat] (E : Catd Z) (z : τ (Obj Z)), Cat;

symbol Fibre [Z : Cat] (E : Catd Z) (z : τ (Obj Z)) : Grpd
≔ Obj (Fibre_cat E z);

unif_rule Obj (@Fibre_cat $Z $E $z) ≡ Obj (@Fibre_cat $Z' $E' $z') ↪ [ $Z ≡ $Z'; $E ≡ $E'; $z ≡ $z' ];
unif_rule Fibre $E $z ≡ Fibre $E' $z' ↪ [ $E ≡ $E'; $z ≡ $z' ];

constant symbol Terminal_catd : Π (Z : Cat), Catd Z;
rule Fibre_cat (Terminal_catd $Z) _ ↪ Terminal_cat;

constant symbol Fibration_cov_catd : Π [Z : Cat], τ (Functor Z Cat_cat) → Catd Z;
rule Fibre_cat (Fibration_cov_catd $M) $z ↪ fapp0 $M $z;

symbol Catd_catd [Z : Cat] (E : Catd Z) : Catd Z;
rule Fibre_cat (Catd_catd $E) $z ↪ Catd_cat (Fibre_cat $E $z);

symbol Pi_cat [Z : Cat] (E : Catd Z) : Cat;

symbol piapp0 : Π [Z : Cat], Π [E : Catd Z],
  Π (s : τ (Obj (Pi_cat E))),
  Π (z : τ (Obj Z)), τ (Fibre E z);

symbol PiHom_catd [Z : Cat] (E : Catd Z)
  (s t : τ (Obj (Pi_cat E))) : Catd Z;
rule Fibre_cat (PiHom_catd $E $s $t) $z
  ↪ Hom_cat (Fibre_cat $E $z) (@piapp0 _ $E $s $z) (@piapp0 _ $E $t $z);

rule Hom_cat (Pi_cat $E) $s $t ↪ Pi_cat (PiHom_catd $E $s $t);

symbol Sigma_cat [Z : Cat] (E : Catd Z) : Cat;
symbol Total_cat [Z : Cat] (E : Catd Z) : Cat ≔ Sigma_cat E;

rule τ (Obj (@Sigma_cat $Z $E))
  ↪ `τΣ_ z : τ (Obj $Z), Obj (Fibre_cat $E z);

injective symbol Sigma_proj1_func [Z : Cat] (E : Catd Z) : τ (Functor (Sigma_cat E) Z);
symbol Total_proj1_func [Z : Cat] (E : Catd Z) : τ (Functor (Total_cat E) Z)
≔ Sigma_proj1_func E;

rule fapp0 (Sigma_proj1_func $E) (Struct_sigma $z $u) ↪ $z;

// Sections into a displayed category are the categorical Pi type.
symbol Functor_catd [Z : Cat] (E D : Catd Z) : Catd Z;
rule Fibre_cat (Functor_catd $E $D) $z
  ↪ Functor_cat (Fibre_cat $E $z) (Fibre_cat $D $z);

symbol Functord_cat [Z : Cat] (E D : Catd Z) : Cat
≔ Pi_cat (Functor_catd E D);

symbol Functord [Z : Cat] (E D : Catd Z) : Grpd
≔ Obj (Functord_cat E D);

rule Hom_cat (Catd_cat $Z) $E $D ↪ Functord_cat $E $D;

symbol id_funcd [Z : Cat] [E : Catd Z] : τ (Functord E E);
rule @id (Catd_cat $Z) $E ↪ @id_funcd $Z $E;

sequential symbol fdapp0 : Π [Z : Cat], Π [E D : Catd Z],
  Π (FF : τ (Functord E D)),
  Π (z : τ (Obj Z)), τ (Fibre E z) → τ (Fibre D z)
;

rule @fdapp0 $Z $E $E (@id_funcd $Z $E) $z $u ↪ $u;
rule @fdapp0 $Z $E $D $FF $z $u
  ↪ @fapp0
      (Fibre_cat $E $z)
      (Fibre_cat $D $z)
      (@piapp0 $Z (@Functor_catd $Z $E $D) $FF $z)
      $u;

constant symbol Transf_cat : Π [A B : Cat], Π (F G : τ (Functor A B)), Cat;

symbol Transf [A B : Cat] (F G : τ (Functor A B)) : Grpd
≔ Obj (@Transf_cat A B F G);

rule Hom_cat (Functor_cat _ _) $F $G ↪ Transf_cat $F $G;

symbol Transf_catd [Z : Cat] [E D : Catd Z]
  (FF GG : τ (Functord E D)) : Catd Z;
rule @Fibre_cat $Z (@Transf_catd $Z $E $D $FF $GG) $z
  ↪ @Transf_cat
      (Fibre_cat $E $z)
      (Fibre_cat $D $z)
      (@piapp0 $Z (@Functor_catd $Z $E $D) $FF $z)
      (@piapp0 $Z (@Functor_catd $Z $E $D) $GG $z);

symbol Transfd_cat [Z : Cat] [E D : Catd Z]
  (FF GG : τ (Functord E D)) : Cat
≔ @Pi_cat Z (@Transf_catd Z E D FF GG);

symbol Transfd [Z : Cat] [E D : Catd Z]
  (FF GG : τ (Functord E D)) : Grpd
≔ Obj (@Transfd_cat Z E D FF GG);

rule @Hom_cat (@Functord_cat $Z $E $D) $FF $GG ↪ @Transfd_cat $Z $E $D $FF $GG;

// -------------------------------------------------------------------------------------------------
// 6. Grothendieck object transport and dependent hom over base arrows
// -------------------------------------------------------------------------------------------------

sequential symbol fib_cov_tapp0_fapp0 : Π [Z : Cat] (M : τ (Functor Z Cat_cat)),
  Π [x y : τ (Obj Z)], Π (f : τ (Hom Z x y)), Π (u : τ (Obj (fapp0 M x))),
  τ (Obj (fapp0 M y));

rule fapp0 (@fapp1_fapp0 $Z Cat_cat $M $x $y $f) $u
  ↪ @fib_cov_tapp0_fapp0 $Z $M $x $y $f $u;

rule @fib_cov_tapp0_fapp0 $Z $M $x $x (id $Z $x) $u ↪ $u;
rule @fib_cov_tapp0_fapp0 $Z $M $y $z $g (@fib_cov_tapp0_fapp0 $Z $M $x $y $f $u)
  ↪ @fib_cov_tapp0_fapp0 $Z $M $x $z (comp_fapp0 $g $f) $u;

sequential symbol Homd_func [Z : Cat] (E : Catd Z)
  (x : τ (Obj Z)) (u : τ (Fibre E x))
  (y : τ (Obj Z)) (v : τ (Fibre E y))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat);

rule @fapp0 (Op_cat (Hom_cat $Z $x $y)) Cat_cat
      (@Homd_func $Z (@Fibration_cov_catd $Z $M) $x $u $y $v)
      $f
  ↪ Hom_cat (fapp0 $M $y)
       (@fib_cov_tapp0_fapp0 $Z $M $x $y $f $u)
       $v;

rule Hom_cat (@Sigma_cat $Z $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_cat
      (@Sigma_cat
        (Op_cat (Hom_cat $Z $x $y))
        (@Fibration_cov_catd
          (Op_cat (Hom_cat $Z $x $y))
          (@Homd_func $Z $E $x $u $y $v)));

// -------------------------------------------------------------------------------------------------
// 7. Initial regression assertions for the v3 skeleton
// -------------------------------------------------------------------------------------------------

assert (Z : Cat) (E : Catd Z) (z : τ (Obj Z)) ⊢
  Fibre_cat (Catd_catd E) z ≡ Catd_cat (Fibre_cat E z);

assert [Z : Cat] (E : Catd Z) (z : τ (Obj Z)) (u : τ (Fibre E z)) ⊢
  fapp0 (Sigma_proj1_func E) (Struct_sigma z u) ≡ z;

assert [Z : Cat] (E : Catd Z) (s t : τ (Obj (Pi_cat E))) (z : τ (Obj Z)) ⊢
  Fibre_cat (PiHom_catd E s t) z ≡ Hom_cat (Fibre_cat E z) (piapp0 s z) (piapp0 t z);

assert [Z : Cat] (E D : Catd Z) ⊢
  Functord_cat E D ≡ Pi_cat (Functor_catd E D);

assert [Z : Cat] (E D : Catd Z) (FF : τ (Functord E D))
  (z : τ (Obj Z)) (u : τ (Fibre E z)) ⊢
  @fdapp0 Z E D FF z u
    ≡ @fapp0
        (Fibre_cat E z)
        (Fibre_cat D z)
        (@piapp0 Z (Functor_catd E D) FF z)
        u;

assert [Z : Cat] (M : τ (Functor Z Cat_cat))
  (x y : τ (Obj Z)) (u : τ (Obj (fapp0 M x))) (v : τ (Obj (fapp0 M y)))
  (f : τ (Hom Z x y)) ⊢
  fapp0 (Homd_func (Fibration_cov_catd M) x u y v) f
    ≡ Hom_cat (fapp0 M y) (@fib_cov_tapp0_fapp0 Z M x y f u) v;
