/* NON-LIBRARY total-duality / negative-section candidate.
   The imported core remains unrepaired. Checks establish local projections
   and the constant-family interface, not the general Homd target or a full
   coherence/consistency result. Do not register as a positive library target.
   See docs/TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md. */
require open emdash.audits.internal_op_co2_prototype;

// Total duality reverses every positive dimension, recursively through Hom.
injective symbol All_cat : Cat → Cat;
rule Obj (All_cat $C) ↪ Obj $C;
rule Hom_cat (All_cat $C) $x $y ↪ All_cat (Hom_cat $C $y $x);
rule All_cat (All_cat $C) ↪ $C;

// The shifted total dual reverses dimensions 2,3,..., but not 1-arrows.
injective symbol CoAll_cat : Cat → Cat;
rule Obj (CoAll_cat $C) ↪ Obj $C;
rule Hom_cat (CoAll_cat $C) $x $y ↪ All_cat (Hom_cat $C $x $y);
rule CoAll_cat (CoAll_cat $C) ↪ $C;
rule All_cat (CoAll_cat $C) ↪ Op_cat $C;
rule CoAll_cat (All_cat $C) ↪ Op_cat $C;

injective symbol All_func [A B : Cat] (F : τ (Functor A B))
  : τ (Functor (All_cat A) (All_cat B));
rule @fapp0 _ _ (@All_func $A $B $F) $x ↪ @fapp0 $A $B $F $x;
rule @fapp1_func _ _ (@All_func $A $B $F) $x $y
  ↪ @All_func (Hom_cat $A $y $x)
      (Hom_cat $B (@fapp0 $A $B $F $y) (@fapp0 $A $B $F $x))
      (@fapp1_func $A $B $F $y $x);
rule @fapp1_fapp0 _ _ (@All_func $A $B $F) $x $y $f
  ↪ @fapp1_fapp0 $A $B $F $y $x $f;
rule @All_func _ _ (@All_func _ _ $F) ↪ $F;

injective symbol CoAll_func [A B : Cat] (F : τ (Functor A B))
  : τ (Functor (CoAll_cat A) (CoAll_cat B));
rule @fapp0 _ _ (@CoAll_func $A $B $F) $x ↪ @fapp0 $A $B $F $x;
rule @fapp1_func _ _ (@CoAll_func $A $B $F) $x $y
  ↪ @All_func (Hom_cat $A $x $y)
      (Hom_cat $B (@fapp0 $A $B $F $x) (@fapp0 $A $B $F $y))
      (@fapp1_func $A $B $F $x $y);
rule @fapp1_fapp0 _ _ (@CoAll_func $A $B $F) $x $y $f
  ↪ @fapp1_fapp0 $A $B $F $x $y $f;

constant symbol all_op : τ (Functor (CoAll_cat Cat_cat) Cat_cat);
rule @fapp0 _ _ all_op $C ↪ All_cat $C;
rule @fapp1_fapp0 _ _ all_op $A $B $F ↪ @All_func $A $B $F;

symbol All_catd [K : Cat] (E : τ (Catd K)) : τ (Catd (CoAll_cat K))
≔ @hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
    (CoAll_cat K) (CoAll_cat Cat_cat) Cat_cat
    all_op (@CoAll_func K Cat_cat E);

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  @fapp0 (CoAll_cat K) Cat_cat (@All_catd K E) k
  ≡ All_cat (@fapp0 K Cat_cat E k);

assert [K : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) ⊢
  @fapp1_fapp0 (CoAll_cat K) Cat_cat (@All_catd K E) x y p
  ≡ @All_func (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y)
      (@fapp1_fapp0 K Cat_cat E x y p);

// Constant-family specialization at the actual postcomposition owner.
rule @hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) _ _ _ all_op
      (@CoAll_func _ _ (@Const_catd $K $C))
  ↪ @Const_catd (CoAll_cat $K) (All_cat $C);

// This uses the original Pi constant-family usability interface.
symbol negative_constant_pi_view [K C : Cat]
  (X : τ (Obj (@Pi_cat (CoAll_cat K) (@All_catd K (@Const_catd K C)))))
  : τ (Functor (Op_cat K) C)
≔ @All_func (CoAll_cat K) (All_cat C) X;

// Candidate for the existing mixed-Hom interface, with actual Pi inputs.
injective symbol Hom_catd_all_negative [K : Cat]
  (E : τ (Catd K))
  (X : τ (Obj (@Pi_cat (CoAll_cat K) (@All_catd K E))))
  (Y : τ (Obj (@Pi_cat K E))) : τ (Catd K);
rule @fapp0 _ _ (@Hom_catd_all_negative $K $E $X $Y) $k
  ↪ Hom_cat (@Fibre_cat $K $E $k)
      (@piapp0 (CoAll_cat $K) (@All_catd $K $E) $X $k)
      (@piapp0 $K $E $Y $k);
rule @Hom_catd_all_negative $K (@Const_catd $K Cat_cat) $X $Y
  ↪ @Functor_catd $K
      (@All_func (CoAll_cat $K) (All_cat Cat_cat) $X) $Y;

assert [K : Cat]
  (X : τ (Obj (@Pi_cat (CoAll_cat K) (@All_catd K (@Const_catd K Cat_cat)))))
  (Y : τ (Obj (@Pi_cat K (@Const_catd K Cat_cat)))) ⊢
  @Hom_catd_all_negative K (@Const_catd K Cat_cat) X Y
  ≡ @Functor_catd K
      (@All_func (CoAll_cat K) (All_cat Cat_cat) X) Y;

// Constant-family sections: dualizing this entire functor gives exactly
// ordinary base contravariance, including all higher base directions.
symbol negative_constant_section_view [K C : Cat]
  (X : τ (Functor (CoAll_cat K) (All_cat C)))
  : τ (Functor (Op_cat K) C)
≔ @All_func (CoAll_cat K) (All_cat C) X;

assert [K C : Cat] (X : τ (Functor (CoAll_cat K) (All_cat C))) ⊢
  @negative_constant_section_view K C X : τ (Functor (Op_cat K) C);

assert [K C : Cat] (X : τ (Functor (CoAll_cat K) (All_cat C)))
  (k : τ (Obj K)) ⊢
  @fapp0 (Op_cat K) C (@negative_constant_section_view K C X) k
  ≡ @fapp0 (CoAll_cat K) (All_cat C) X k;

// Contrast: pointwise 1-opposite followed by ordinary opposite keeps Co2(K).
assert [K C : Cat] (X : τ (Functor (Co2_cat K) (Op_cat C))) ⊢
  @Op_func (Co2_cat K) (Op_cat C) X
  : τ (Functor (Op_cat (Co2_cat K)) C);
assertnot [K C : Cat] (X : τ (Functor (Co2_cat K) (Op_cat C))) ⊢
  @Op_func (Co2_cat K) (Op_cat C) X : τ (Functor (Op_cat K) C);

// Neither total nor shifted-total duality is a truncation.
assert [C : Cat] [x y : τ (Obj C)] [f g : τ (Hom C x y)] ⊢
  Hom_cat (Hom_cat (CoAll_cat C) x y) f g
  ≡ All_cat (Hom_cat (Hom_cat C x y) g f);

assert [C : Cat] [x y : τ (Obj C)] [f g : τ (Hom C x y)]
  [a b : τ (Hom (Hom_cat C x y) g f)] ⊢
  Hom_cat (Hom_cat (Hom_cat (CoAll_cat C) x y) f g) a b
  ≡ All_cat (Hom_cat (Hom_cat (Hom_cat C x y) g f) b a);
