/*
  m— / emdash2
  Functorial programming for (strict/lax) ω-categories in Lambdapi.
*/

flag "eta_equality" on;

// `TYPE` is lambdapi-framework (meta-) type for collections;
// so in the object-lamguage, i.e. emdah, any `ABC : TYPE` means that `ABC` is a collection/grammar-entity to collect/classify some things
// A minimal `Grpd : TYPE` + decoding function `τ : Grpd → TYPE`,
// `Grpd` (often written `Set` in the Lambdapi doc) is the (meta-)collection of ω-groupoid (or "sets" for ease of understanding), similar as in hott homotopy type theory.
constant symbol Grpd : TYPE;
injective symbol τ : Grpd → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Grpd;
builtin "P" ≔ τ;

constant symbol = : Π [a: Grpd], τ a → τ a → Grpd; /* here `=` ends in `Grpd` ω-groupoid instead of the usual `Prop` (the `Set` in the Lambdapi doc uses a `=` which lands in `Prop`) */
notation = infix 10;

constant symbol eq_refl : Π [a: Grpd], Π x: τ a, τ (x = x);
symbol ind_eq : Π [a: Grpd], Π [x: τ a], Π [y: τ a], τ (x = y) → Π p: (τ a → Grpd), τ (p y) → τ (p x);
rule ind_eq (eq_refl $x) $p $u ↪ $u;
builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

// A tiny inhabited type, useful for “always-true” unification-rule conditions.
// unif_rule A $x ≡ B $x ↪ [ tt ≡ tt ]
inductive unit : TYPE ≔ | tt : unit;

// Minimal naturals (dimension index).
inductive Nat : TYPE ≔
| Z : Nat
| S : Nat → Nat;

// # --- Categories ---

// `Cat` is the collection of categories
constant symbol Cat : TYPE;

// `Obj` is the underlying/core groupoid of a category
injective symbol Obj : Cat → Grpd;

// `Hom` is the category of morphisms of a (omega-)category
injective symbol Hom : Π [A : Cat] (X:  τ (Obj A)) (Y: τ (Obj A)), Cat;


// # --- Functors ---

// `Functor` is the category of functors between categories
constant symbol Functor : Π(A : Cat), Π(B : Cat), Cat;

// `fapp0` is the application of a functor to an object
symbol fapp0 : Π[A : Cat], Π[B : Cat], Π(F : τ (Obj (Functor A B))), τ (Obj A) → τ (Obj B);
// `fapp1` is the application of a functor to a morphism
symbol fapp1 : Π[A : Cat], Π[B : Cat], Π(F : τ (Obj (Functor A B))),
  Π[X: τ (Obj A)], Π[Y: τ (Obj A)], τ (Obj (Functor (Hom X Y) (Hom (fapp0 F X) (fapp0 F Y))));

// # --- Grpd_cat category classifier, discrete fibrations, yoneda representable Functor ---

// `Grpd_cat` is the category of types/sets/groupoids,
// classifier for discrete modules/fibrations; where a discrete fibration is a functor in `Functor (A, Grpd_cat)`
constant symbol Grpd_cat : Cat;

unif_rule τ (Obj $A) ≡ Grpd ↪ [ $A ≡ Grpd_cat ];

// see below section "extensionality for Grpd_cat" for structure-preservation
rule τ (Obj (@Hom Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);

// # --- Cat category classifier, fibrations, isofibrations, yoneda representable Functor ---

// `Cat_cat` is the category of categories, classifier for non-discrete fibrations; 
// where a non-discreate fibration is a functor in `Functor (A, Cat_cat)`
constant symbol Cat_cat : Cat;

unif_rule τ (Obj $A) ≡ Cat ↪ [ $A ≡ Cat_cat ];

// arrows in `Cat_cat` are functors (precisely: the Hom-category of the category of categories is same as the Functor category)
rule @Hom Cat_cat $X $Y ↪ Functor $X $Y;

// `identity_functor` is the identity functor
// this can and will be defined in terms of `identity_morph` of Cat_cat
constant symbol identity_functor [A:Cat]: τ ( Obj (Functor A A));
// composition of functors
// TODO: define in terms of `compose_morph` of Cat_cat
symbol compose_functors [A:Cat] [B:Cat] [C:Cat] (F: τ (Obj (Functor B C))) (G: τ (Obj (Functor A B))) : τ (Obj (Functor A C));

// yoneda/hom covariant embedding functor to Cat_cat; also TODO: contravariant Yoneda
// so `@hom_cov A W _ F` (which is a functor in `Functor (A, Cat_cat)`)  is in the usual-notation the same as `Hom_A(W, F -)` 
// that is Hom precomposed with F at the covariant argument
constant symbol hom_cov : Π [A : Cat], Π (W: τ (Obj A)), Π [B : Cat], Π (F : τ (Obj (Functor B A))), τ (Obj (Functor B Cat_cat));

rule fapp0 (hom_cov $X $F) $Y ↪ Hom $X (fapp0 $F $Y);


// # --- Dependent categories (isofibrations) ---

// isofibration E: Catd A has semantics : a functor E -> A that is Functor(E, A).
constant symbol Catd : Π(A : Cat), TYPE;

constant symbol Terminal_catd : Π(A : Cat), Catd A;

// Grothendieck construction / “category of elements” for (covariant/cartesian) fibrations ( Cat-valued functors ) :
// a (cartesian) fibration E : A → Cat gives an (iso)fibration ∫E → A, i.e. an element of Catd A.
constant symbol IsoFibration_catd :
  Π [A : Cat], τ (Obj (Functor A Cat_cat)) → Catd A;



// `Functord F E ` is a dependent functor, which is a section of E (of shape F);
// so it is the usual Pi-Product Π in the context of proof assistants:
// so if F was B (terminal/identity fibration), then `Functord F E` is `Π(xB : B) E(xB)`
constant symbol Functord : Π[B : Cat], Π(F : Catd B), Π(E : Catd B), Cat;

// dependent/fibred identity functor
constant symbol identity_functord [Z : Cat] [A:Catd Z]: τ ( Obj (Functord A A));
// dependent/fibred composition of functors
symbol compose_functorsd [Z : Cat] [A:Catd Z] [B:Catd Z] [C:Catd Z] (F: τ ( Obj (Functord B C))) (G: τ (Obj (Functord A B))) : 
τ ( Obj (Functord A C));


// `Fibre_cat E xB` is the fibre of the fibration E at xB : B
// TODO: review `injective` here
injective symbol Fibre_cat : Π[B : Cat] (E : Catd B) (xB : τ (Obj B)), Cat;

// Fibre_cat of the Grothendieck construction recovers the original Cat-valued functor.
rule Fibre_cat (IsoFibration_catd $M) $x ↪ fapp0 $M $x;

// Pullback of a dependent category / fibration:
// Pullback_catd E F is the pullback of E : Catd B along F : Functor(A,B).
constant symbol Pullback_catd :
  Π [A : Cat] [B : Cat], Catd B → τ (Obj (Functor A B)) → Catd A;
rule Fibre_cat (Pullback_catd $E $F) $xA ↪ Fibre_cat $E (fapp0 $F $xA);

// # --- Natural Transformations ---

// `Transf` is the category of natural transformations between functors
constant symbol Transf : Π [A : Cat], Π [B : Cat], Π (F : τ (Obj (Functor A B))), Π (G : τ (Obj (Functor A B))), Cat;

// To iterate `Transf` so to get omega-categories, we need to be able to "see"/reinterpret a natural transformation somehow as a (fibred/dependent) functor so that we can again iterate `Transf` of `Transf`-as-functor...
// notation:  (ϵ)._X  for  tapp ϵ X
symbol tapp : Π [A : Cat], Π [B : Cat], Π [F G : τ (Obj (Functor A B))],
  Π (ϵ : τ (Obj (Transf F G))), Π (X: τ (Obj A)), 
  τ (Obj (Functord (IsoFibration_catd (hom_cov X (@identity_functor A))) (IsoFibration_catd (hom_cov (fapp0 F X) G))));

rule @Hom (Functor _ _) $F $G ↪ Transf $F $G;


// dependent sum/sigma type
inductive τΣ_ [a : Grpd] (P : τ a → Grpd) : TYPE ≔
| Struct_sigma [a P] : Π (sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst) ), @τΣ_ a P;
notation τΣ_ quantifier;
constant symbol Σ_ [a : Grpd] (P : τ a → Grpd) : Grpd; notation Σ_ quantifier;
rule τ (Σ_ $P) ↪ τΣ_ $P;

// first projection of dependent sum/sigma type
injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;

// second projection of dependent sum/sigma type
injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;



// Total_cat' is the total space of a isofibration `M : Catd A` that is a Functor(M, A) 
// it is also known as `Context_cat` in `cartierSolution13.lp`, the context extension of A by the dependent type/category M over A
constant symbol Total_cat' [A : Cat] (M: Catd A): Cat;

// first projection of Total_cat' to base category
injective symbol Total_cat'_proj [A : Cat] (M: Catd A): τ (Obj (Functor (Total_cat' M) A));

// second dependent projection of Total_cat' to the fibre at the first projection
injective symbol Total_cat'_projd [A : Cat] (M: Catd A):
  τ (Obj (Functord (Terminal_catd (Total_cat' M)) (Pullback_catd M (Total_cat'_proj M))));

// objects of the total category: Σ x:A, (objects in the fibre over x)
rule τ (Obj (Total_cat' $M)) ↪ `τΣ_ X : τ (Obj _), Obj (Fibre_cat $M X);


// Total_cat is the total space of a fibration M : A -> Cat_cat and is definable via Total_cat' and the Grothendieck construction.
symbol Total_cat [A : Cat] (M: τ (Obj (Functor A Cat_cat))): Cat;

// first projection of Total_cat to base category
injective symbol Total_cat_proj [A : Cat] (M: τ (Obj (Functor A Cat_cat))): τ (Obj (Functor (Total_cat M) A));

// second dependent projection of Total_cat to the fibre at the first projection
injective symbol Total_cat_projd [A : Cat] (M: τ (Obj (Functor A Cat_cat))):
  τ (Obj (Functord (Terminal_catd (Total_cat M)) (Pullback_catd (IsoFibration_catd M) (Total_cat_proj M))));

// Total_cat is definable via Total_cat' and the Grothendieck construction.
rule Total_cat $M ↪ Total_cat' (IsoFibration_catd $M);
rule Total_cat_proj $M ↪ Total_cat'_proj (IsoFibration_catd $M);
rule Total_cat_projd $M ↪ Total_cat'_projd (IsoFibration_catd $M);


// opposite category

injective symbol Op_cat : Cat → Cat;

rule Op_cat (Op_cat $A) ↪ $A;

constant symbol Terminal_cat : Cat;

injective symbol Terminal_func :  Π (A : Cat), τ (Obj (Functor A Terminal_cat));

constant symbol Terminal_obj : τ (Obj Terminal_cat); 
//elim rule, rename Terminal_elim_func ?
injective symbol Obj_func : Π [Y : Cat], τ (Obj Y) → τ (Obj (Functor Terminal_cat Y));

//computation rule, obj
rule fapp0 (Obj_func $F) $M ↪  $F;


// product category
injective symbol Product_cat : Π (U : Cat) (A : Cat), Cat;

// first/left projection of the product category
symbol Product_projL_func : Π [A1 A2 B: Cat], τ (Obj (Functor B (Product_cat A1 A2))) → τ (Obj (Functor B A1));
// second/right projection of the product category
symbol Product_projR_func : Π [A1 A2 B: Cat], τ (Obj (Functor B (Product_cat A1 A2))) → τ (Obj (Functor B A2));
// pairing of the product category
injective symbol Product_pair_func : Π [A1 A2 I : Cat] (F : τ (Obj (Functor I A1))) (G : τ (Obj (Functor I A2))),
  τ (Obj (Functor I (Product_cat A1 A2)));

// Product category: object-level projections/pairing (usual category theory interface).
// (Rewrite/computation rules deferred for now.)
symbol Product_projL : Π [A1 A2 : Cat], τ (Obj (Product_cat A1 A2)) → τ (Obj A1);
symbol Product_projR : Π [A1 A2 : Cat], τ (Obj (Product_cat A1 A2)) → τ (Obj A2);
injective symbol Product_pair : Π [A1 A2 : Cat] (X : τ (Obj A1)) (Y : τ (Obj A2)),
  τ (Obj (Product_cat A1 A2));



// fibred product category
injective symbol Product_catd : Π [Z : Cat] (U : Catd Z) (A : Catd Z), Catd Z;

// Fibred product (over the same base Z): computed fibrewise.
rule Fibre_cat (Product_catd $U $A) $xZ ↪ Product_cat (Fibre_cat $U $xZ) (Fibre_cat $A $xZ);

// Dependent projections / pairing (fibred functoriality).
symbol Product_projL_functord :
  Π [Z : Cat] [U A : Catd Z], τ (Obj (Functord (Product_catd U A) U));
symbol Product_projR_functord :
  Π [Z : Cat] [U A : Catd Z], τ (Obj (Functord (Product_catd U A) A));
injective symbol Product_pair_functord :
  Π [Z : Cat] [U A B : Catd Z]
    (F : τ (Obj (Functord B U))) (G : τ (Obj (Functord B A))),
    τ (Obj (Functord B (Product_catd U A)));


    // notation: id
// `identity_morph` is the identity in categories
injective symbol identity_morph : Π[A : Cat], Π(X: τ (Obj A)), τ (Obj (Hom X X));

// composition morphism
// notation:  `f ∘> g`   or   `g <∘ f`   for  `compose_morph g f`
symbol compose_morph : Π [A : Cat], Π [X: τ (Obj A)], Π [Y: τ (Obj A)], Π [Z: τ (Obj A)], τ (Obj (Functor (Product_cat (Hom Y Z) (Hom X Y)) (Hom X Z)));

// composition morphism, the `fapp0` part
symbol compose_morph_fapp0 : Π [A : Cat], Π [X: τ (Obj A)], Π [Y: τ (Obj A)], Π [Z: τ (Obj A)], Π (g: τ (Obj (Hom Y Z))), Π (f: τ (Obj (Hom X Y))),  τ (Obj (Hom X Z));

// TODO: redo: rule (fapp0 (@compose_morph $A $X $Y $Z)) (Product_pair $g $f) ↪ @compose_morph_fapp0 $A $X $Y $Z $g $f;

// --- draft experiments from here ---

// yoneda/hom for dependent category
constant symbol homd_cov :  Π [Z : Cat], Π [A : Catd Z] [W_: τ (Obj Z)] (W: τ (Obj (Fibre_cat A W_))), Π [B : Catd Z], Π (F : τ (Obj (Functord B A))),
τ (Obj (Functor (Total_cat' (Product_catd B (IsoFibration_catd (hom_cov W_ (@identity_functor Z))) /*TODO: ^op */ )) Cat_cat));

// keep both fapp1d and fapp1 ? fapp1 is the fapp0 of the result of fapp1d
symbol fapp1d : Π[A : Cat], Π[B : Cat], Π(F : τ (Obj (Functor A B))),
  Π[X: τ (Obj A)], τ (Obj (Functord (IsoFibration_catd (hom_cov X (@identity_functor A))) (IsoFibration_catd (hom_cov (fapp0 F X) F))));

// `dfapp0` is the application of a fibred/dependent functor to an object
symbol dfapp0 : Π[Z : Cat], Π[A : Catd Z], Π[B : Catd Z], Π(F : τ (Obj (Functord A B))), Π[xZ : τ (Obj Z)], τ (Obj (Fibre_cat A xZ)) → τ (Obj (Fibre_cat B xZ));

// `dfapp1d` is the application of a fibred/dependent functor to a morphism
symbol dfapp1d : Π[Z : Cat], Π[A : Catd Z], Π[B : Catd Z], Π(F : τ (Obj (Functord A B))), Π [X_: τ (Obj Z)] (X: τ (Obj (Fibre_cat A X_))),
   τ (Obj (Functord (IsoFibration_catd (homd_cov X (@identity_functord _ A))) (IsoFibration_catd (homd_cov (dfapp0 F X) F))));

