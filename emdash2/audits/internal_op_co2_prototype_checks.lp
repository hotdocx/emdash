/* NON-LIBRARY PROTOTYPE CHECKS: local projections and wrong-direction
   rejection, not a consistency certificate or completed kernel repair. */
require open emdash.audits.internal_op_co2_prototype;

assert [C : Cat] [x y : τ (Obj C)] ⊢
  Hom_cat (Co2_cat C) x y ≡ Op_cat (Hom_cat C x y);

// Dimension 2 reverses; its Hom category still contains all higher cells.
assert [C : Cat] [x y : τ (Obj C)]
  [f g : τ (Hom C x y)] ⊢
  Hom_cat (Hom_cat (Co2_cat C) x y) f g
  ≡ Hom_cat (Hom_cat C x y) g f;

// Dimension 3 is not reversed or erased.
assert [C : Cat] [x y : τ (Obj C)] [f g : τ (Hom C x y)]
  [a b : τ (Hom (Hom_cat C x y) g f)] ⊢
  Hom_cat (Hom_cat (Hom_cat (Co2_cat C) x y) f g) a b
  ≡ Hom_cat (Hom_cat (Hom_cat C x y) g f) a b;

assert [C : Cat] ⊢ Co2_cat (Co2_cat C) ≡ C;
assert [A B : Cat] (F : τ (Functor A B)) [x y : τ (Obj A)] ⊢
  @fapp1_func (Co2_cat A) (Co2_cat B) (@Co2_func A B F) x y
  ≡ @Op_func (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y);

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @fapp0 (Op_cat (Functor_cat A B))
    (Functor_cat (Op_cat A) (Op_cat B)) (op_co2_hom_func A B) F
  ≡ @Op_func A B F;

assert [A B : Cat] [F G : τ (Functor A B)] (eta : τ (Transf F G)) ⊢
  @fapp0 (@Transf_cat A B F G)
    (@Transf_cat (Op_cat A) (Op_cat B)
      (@Op_func A B G) (@Op_func A B F))
    (@op_co2_transf_func A B F G) eta
  ≡ @Op_transf A B F G eta;

// The retained whole next action accepts arbitrary modifications.
assert [A B : Cat] [F G : τ (Functor A B)]
  [eta theta : τ (Transf F G)] ⊢
  @fapp1_func (@Transf_cat A B F G)
    (@Transf_cat (Op_cat A) (Op_cat B)
      (@Op_func A B G) (@Op_func A B F))
    (@op_co2_transf_func A B F G) eta theta
  : τ (Functor
      (Hom_cat (@Transf_cat A B F G) eta theta)
      (Hom_cat (@Transf_cat (Op_cat A) (Op_cat B)
          (@Op_func A B G) (@Op_func A B F))
        (@Op_transf A B F G eta) (@Op_transf A B F G theta)));

// Corrected opposite families keep ordinary fibre/arrow formulas.
assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) ⊢
  @fapp0 (Co2_cat K) Cat_cat (@op_co2_catd K E) k
  ≡ Op_cat (@fapp0 K Cat_cat E k);

assert [K : Cat] (E : τ (Catd K)) [x y : τ (Obj K)]
  (p : τ (Hom K x y)) ⊢
  @fapp1_fapp0 (Co2_cat K) Cat_cat (@op_co2_catd K E) x y p
  ≡ @Op_func (@fapp0 K Cat_cat E x) (@fapp0 K Cat_cat E y)
      (@fapp1_fapp0 K Cat_cat E x y p);

// Pair the positive eta computation with rejection of its wrong endpoints.
assertnot [A B : Cat] [F G : τ (Functor A B)]
  (eta : τ (Transf F G)) ⊢
  @Op_transf A B F G eta
  : τ (Transf (@Op_func A B F) (@Op_func A B G));

// Original diagnostic input is not an arrow in the corrected hom source.
assertnot [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y)) ⊢
  @fapp1_fapp0
    (Op_cat (Functor_cat Terminal_cat C))
    (Functor_cat Terminal_cat (Op_cat C))
    (op_co2_hom_func Terminal_cat C)
    (@Obj_func C x) (@Obj_func C y)
    (@Const_transf Terminal_cat C x y f)
  : τ (Transf
      (@Op_func Terminal_cat C (@Obj_func C x))
      (@Op_func Terminal_cat C (@Obj_func C y)));

// The direction-correct route returns the original arrow, not a reverse.
symbol op_co2_reinterpret
  [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  : τ (Hom C x y)
≔ @tapp0_fapp0 Terminal_cat (Op_cat C)
    (@Op_func Terminal_cat C (@Obj_func C y))
    (@Op_func Terminal_cat C (@Obj_func C x)) Terminal_obj
    (@fapp1_fapp0
      (Op_cat (Functor_cat Terminal_cat C))
      (Functor_cat Terminal_cat (Op_cat C))
      (op_co2_hom_func Terminal_cat C)
      (@Obj_func C y) (@Obj_func C x)
      (@Const_transf Terminal_cat C x y f));

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y)) ⊢
  @op_co2_reinterpret C x y f ≡ f;
