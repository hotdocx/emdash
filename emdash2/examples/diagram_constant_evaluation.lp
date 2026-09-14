require open emdash.emdash3_2_diagram_evaluation;
symbol K : Cat;
symbol I : Cat;
symbol C : Cat;
symbol D : τ (Functor I C);
symbol i : τ (Obj I);
symbol x : τ (Obj K);
symbol y : τ (Obj K);
symbol v : τ (Obj C);
symbol L : Cat;
symbol F : τ (Functor L (Functor_cat I C));
symbol l : τ (Obj L);

// The whole constant parameter family is the chosen normal form.
assert ⊢ @sym_fapp0_func K I C (@Const_func K (Functor_cat I C) D) i
  ≡ @Const_func K C (@fapp0 I C D i);
// Evaluate before or after projecting to the complete Hom functor.
assert ⊢ @fapp1_func K C (@sym_fapp0_func K I C (@Const_func K (Functor_cat I C) D) i) x y
  ≡ @fapp1_func K C (@Const_func K C (@fapp0 I C D i)) x y;
assert ⊢ @sym_fapp0_fapp1_func K I C (@Const_func K (Functor_cat I C) D) i x y
  ≡ @fapp1_func K C (@Const_func K C (@fapp0 I C D i)) x y;
// Constant precomposition and whole shape evaluation join in either order.
assert ⊢ @sym_fapp0_func K I C
    (@comp_cat_fapp0 K L (Functor_cat I C) F (@Const_func K L l)) i
  ≡ @Const_func K C (@fapp0 I C (@fapp0 L (Functor_cat I C) F l) i);
assert ⊢ @sym_fapp0_fapp1_func K I C
    (@comp_cat_fapp0 K L (Functor_cat I C) F (@Const_func K L l)) i x y
  ≡ @fapp1_func K C (@Const_func K C (@fapp0 I C (@fapp0 L (Functor_cat I C) F l) i)) x y;
// No unrelated selected value is substituted.
assertnot ⊢ @sym_fapp0_func K I C (@Const_func K (Functor_cat I C) D) i ≡ @Const_func K C v;
