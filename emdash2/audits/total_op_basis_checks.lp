/* NON-LIBRARY prefix audit. Run only through scripts/check_total_op_prefix.sh.
   The complete Homd target and downstream kernel are not yet migrated. */
require open emdash.emdash3_2;

assert [C : Cat] [x y : τ (Obj C)] ⊢
  Hom_cat (Op_cat C) x y ≡ Op_cat (Hom_cat C y x);
assert [C : Cat] [x y : τ (Obj C)] ⊢
  Hom_cat (CoAbove2_cat C) x y ≡ Op_cat (Hom_cat C x y);
assert [C : Cat] [x y : τ (Obj C)] ⊢
  Hom_cat (Transpose_cat C) x y ≡ Hom_cat C y x;
assert [C : Cat] ⊢ Transpose_cat (Transpose_cat C) ≡ C;

assert [C : Cat] [x y : τ (Obj C)] [f g : τ (Hom C y x)] ⊢
  Hom_cat (Hom_cat (Op_cat C) x y) f g
  ≡ Op_cat (Hom_cat (Hom_cat C y x) g f);
assert [C : Cat] [x y : τ (Obj C)] [f g : τ (Hom C y x)] ⊢
  Hom_cat (Hom_cat (Transpose_cat C) x y) f g
  ≡ Hom_cat (Hom_cat C y x) f g;
assertnot [C : Cat] ⊢ Op_cat C ≡ Transpose_cat C;

// Total duality continues at the third dimension; the tower is not capped.
assert [C : Cat] [x y : τ (Obj C)] [f g : τ (Hom C y x)]
  [alpha beta : τ (Hom (Hom_cat C y x) g f)] ⊢
  Hom_cat (Hom_cat (Hom_cat (Op_cat C) x y) f g) alpha beta
  ≡ Op_cat (Hom_cat (Hom_cat (Hom_cat C y x) g f) beta alpha);

assert ⊢ op : τ (Functor (CoAbove2_cat Cat_cat) Cat_cat);
assertnot ⊢ op : τ (Functor Cat_cat Cat_cat);
assert ⊢ @Op_catd Cat_cat (@id_func Cat_cat)
  : τ (Functor (CoAbove2_cat Cat_cat) Cat_cat);
assertnot ⊢ @Op_catd Cat_cat (@id_func Cat_cat) : τ (Functor Cat_cat Cat_cat);

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @fapp1_fapp0 (CoAbove2_cat Cat_cat) Cat_cat op A B F
  ≡ @Op_func A B F;
assert [A B : Cat] [F G : τ (Functor A B)] (eta : τ (Transf G F)) ⊢
  @fapp1_fapp0 _ _ (@fapp1_func (CoAbove2_cat Cat_cat) Cat_cat op A B)
    F G eta
  ≡ @Op_transf A B G F eta;

// A further whole action remains available after the transformation layer.
type λ A : Cat, λ B : Cat, λ F : τ (Functor A B), λ G : τ (Functor A B),
  @fapp1_func _ _ (@fapp1_func (CoAbove2_cat Cat_cat) Cat_cat op A B) F G;

// Both total and ordinary-transpose functors retain the appropriate whole Hom.
assert [A B : Cat] (F : τ (Functor A B)) [x y : τ (Obj A)] ⊢
  @fapp1_func _ _ (@Op_func A B F) x y
  ≡ @Op_func _ _ (@fapp1_func A B F y x);
// A transparent canonical-endpoint view avoids the raw assert's eager
// type decomposition. It adds no new conversion or proof-time rule.
symbol transpose_hom_action_typed [A B : Cat] (F : τ (Functor A B))
  [x y : τ (Obj A)]
  : τ (Functor (Hom_cat A y x)
      (Hom_cat B (@fapp0 A B F y) (@fapp0 A B F x)))
≔ @fapp1_func (Transpose_cat A) (Transpose_cat B) (@Transpose_func A B F) x y;

assert [A B : Cat] (F : τ (Functor A B)) [x y : τ (Obj A)] ⊢
  @transpose_hom_action_typed A B F x y
  ≡ @fapp1_func A B F y x;

assert [K : Cat] (E : τ (Catd K)) [x : τ (Obj K)] ⊢
  @fapp0 _ _ (@Op_catd K E) x ≡ Op_cat (@Fibre_cat K E x);

assert [K : Cat] (E : τ (Catd K)) ⊢
  @Op_catd (CoAbove2_cat K) (@Op_catd K E) ≡ E;
assert [K : Cat] [E D : τ (Catd K)] (FF : τ (Functord E D)) ⊢
  @Op_funcd (CoAbove2_cat K) (@Op_catd K E) (@Op_catd K D)
    (@Op_funcd K E D FF)
  ≡ FF;

assert [A B : Cat] [F G : τ (Functor A B)] (eta : τ (Transf F G))
  [x y : τ (Obj A)] ⊢
  @tapp1_func _ _ _ _ x y (@Op_transf A B F G eta)
  ≡ @Op_func _ _ (@tapp1_func A B F G y x eta);
assert [K : Cat] [E D : τ (Catd K)] (FF : τ (Functord E D)) [x : τ (Obj K)] ⊢
  @tapp0_fapp0 _ _ _ _ x
    (@fapp1_fapp0 _ _ (Op_catd_func K) E D FF)
  ≡ @Op_func (@Fibre_cat K E x) (@Fibre_cat K D x)
      (@tapp0_fapp0 K Cat_cat E D x FF);

// The corrected family maps a genuine reversed base 2-cell, not only arrows.
assert [K : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  [p q : τ (Hom K x y)] (alpha : τ (Hom (Hom_cat K x y) q p)) ⊢
  @fapp1_fapp0
    (Op_cat (Hom_cat K x y))
    (Functor_cat (Op_cat (@Fibre_cat K E x)) (Op_cat (@Fibre_cat K E y)))
    (@fapp1_func (CoAbove2_cat K) Cat_cat (@Op_catd K E) x y) p q alpha
  ≡ @Op_transf (@Fibre_cat K E x) (@Fibre_cat K E y)
      (@fapp1_fapp0 K Cat_cat E x y q) (@fapp1_fapp0 K Cat_cat E x y p)
      (@fapp1_fapp0 _ _ (@fapp1_func K Cat_cat E x y) q p alpha);

// Constant negative sections use the same total op and the derived transpose.
symbol total_negative_section_view [K C : Cat]
  (X : τ (Obj (@Pi_cat (CoAbove2_cat K) (@Op_catd K (@Const_catd K C)))))
  : τ (Functor (Transpose_cat K) C)
≔ @Op_func (CoAbove2_cat K) (Op_cat C) X;

assert [K C : Cat]
  (X : τ (Obj (@Pi_cat (CoAbove2_cat K) (@Op_catd K (@Const_catd K C)))))
  [k : τ (Obj K)] ⊢
  @fapp0 (Transpose_cat K) C (@total_negative_section_view K C X) k
  ≡ @fapp0 (CoAbove2_cat K) (Op_cat C) X k;
