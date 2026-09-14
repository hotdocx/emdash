/* Reindexing retains original paired inputs, operations and selected mate data. */
require open emdash.emdash3_2_one_cat_biproduct_family_reindex;

assert [A B C D : Cat] (U : τ (Functor A B)) (F : τ (Functor B C)) (G : τ (Functor B D)) ⊢ @eq_refl (Functor A
  (Product_cat C D)) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A D) (@comp_cat_fapp0 A B C F U)
  (@comp_cat_fapp0 A B D G U)) : τ (@= (Functor A (Product_cat C D)) (@comp_cat_fapp0 A B (Product_cat C D)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B D) F G) U) (@Struct_sigma (Functor A C) (λ _ : τ
  (Functor A C), Functor A D) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B D G U)));
assertnot [A B C D : Cat] (U : τ (Functor A B)) (F : τ (Functor B C)) (G : τ (Functor B D)) (U0 : τ (Functor A B)) ⊢
  @eq_refl (Functor A (Product_cat C D)) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A D)
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B D G U)) : τ (@= (Functor A (Product_cat C D)) (@comp_cat_fapp0 A B
  (Product_cat C D) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B D) F G) U) (@Struct_sigma (Functor
  A C) (λ _ : τ (Functor A C), Functor A D) (@comp_cat_fapp0 A B C F U0) (@comp_cat_fapp0 A B D G U0)));
assert [A B C : Cat] (Prod : τ (Functor (Product_cat C C) C)) (U : τ (Functor A B)) (F G : τ (Functor B C)) ⊢ @eq_refl
  (Functor A C) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C
  Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0
  A B C G U))) : τ (@= (Functor A C) (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A
  C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U))));
assertnot [R L : Cat] (F : τ (Functor R L)) (G : τ (Functor L R)) (J J0 : τ (@Adjunction R L F G)) (x : τ (Obj R)) (y
  : τ (Obj L)) (h : τ (Obj (Hom_cat L (@fapp0 R L F x) y))) ⊢ @eq_refl (Obj (Hom_cat R x (@fapp0 L R G y))) (@fapp0
  (Hom_cat L (@fapp0 R L F x) y) (Hom_cat R x (@fapp0 L R G y)) (@adjunction_transpose_func R L F G J x y) h) : τ (@=
  (Obj (Hom_cat R x (@fapp0 L R G y))) (@fapp0 (Hom_cat L (@fapp0 R L F x) y) (Hom_cat R x (@fapp0 L R G y))
  (@adjunction_transpose_func R L F G J x y) h) (@fapp0 (Hom_cat L (@fapp0 R L F x) y) (Hom_cat R x (@fapp0 L R G y))
  (@adjunction_transpose_func R L F G J0 x y) h));
assertnot [R L : Cat] (F : τ (Functor R L)) (G : τ (Functor L R)) (J J0 : τ (@Adjunction R L F G)) (x : τ (Obj R)) (y
  : τ (Obj L)) (h : τ (Obj (Hom_cat R x (@fapp0 L R G y)))) ⊢ @eq_refl (Obj (Hom_cat L (@fapp0 R L F x) y)) (@fapp0
  (Hom_cat R x (@fapp0 L R G y)) (Hom_cat L (@fapp0 R L F x) y) (@adjunction_untranspose_func R L F G J x y) h) : τ
  (@= (Obj (Hom_cat L (@fapp0 R L F x) y)) (@fapp0 (Hom_cat R x (@fapp0 L R G y)) (Hom_cat L (@fapp0 R L F x) y)
  (@adjunction_untranspose_func R L F G J x y) h) (@fapp0 (Hom_cat R x (@fapp0 L R G y)) (Hom_cat L (@fapp0 R L F x)
  y) (@adjunction_untranspose_func R L F G J0 x y) h));
assert [A B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (V : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (U : τ (Functor A B)) (X Y : τ (Functor
  B C)) (f g : τ (@Transf B C X Y)) ⊢ @one_cat_additive_family_reindex_path A B C C1 Prod t V T0 U X Y f g : τ (@=
  (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U
  X Y) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y f g)) (@one_cat_additive_family_add A C C1 Prod t V T0
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)));
assert [A B C : Cat] (U : τ (Functor A B)) (X : τ (Functor B C)) ⊢ @prewhisker_identity_path A B C U X : τ (@=
  (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)) (@fapp0 (@Transf_cat B C X X) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)) (@comp_cat_con_fapp1_func A B C U X X) (@id (Functor_cat B
  C) X)) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)));
assert [A B D C : Cat] (V : τ (Functor A B)) (U : τ (Functor B D)) (F G : τ (Functor D C)) (h : τ (@Transf D C F G)) ⊢
  @prewhisker_assoc_path A B D C V U F G h : τ (@= (@Transf A C (@comp_cat_fapp0 A D C F (@comp_cat_fapp0 A B D U V))
  (@comp_cat_fapp0 A D C G (@comp_cat_fapp0 A B D U V))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C V
  (@comp_cat_fapp0 B D C F U) (@comp_cat_fapp0 B D C G U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B D C U F G) h))
  (@fapp0 _ _ (@comp_cat_con_fapp1_func A D C (@comp_cat_fapp0 A B D U V) F G) h));

// Independent restricted coordinates exercise the actual product-mate consumer.
assert [A B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (U : τ (Functor A B)) (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf
  B C X G))
  ⊢ @one_cat_product_pair_reindex_path A B C C1 Prod BP U X F G f g
    : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C)
  (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
  (@one_cat_product_family_pair B C C1 Prod BP X F G f g)) (@one_cat_product_family_pair A C C1 Prod BP
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@fapp0 (@Transf_cat B C X F)
  (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) f)
  (@fapp0 (@Transf_cat B C X G) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))
  (@comp_cat_con_fapp1_func A B C U X G) g)));

// The coproduct consumer retains both original whole inputs.
assert [A B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (V : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (U : τ (Functor A B)) (F G Y : τ
  (Functor B C)) (f : τ (@Transf B C F Y)) (g : τ (@Transf B C G Y))
  ⊢ @one_cat_copair_reindex_path A B C C1 Prod t V T0 U F G Y f g
    : τ (@= (@Transf A C (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A
  (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F
  U) (@comp_cat_fapp0 A B C G U))) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  Y) (@one_cat_copair_family B C C1 Prod t V T0 F G Y f g)) (@one_cat_copair_family A C C1 Prod t V T0
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C F Y)
  (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U F Y) f)
  (@fapp0 (@Transf_cat B C G Y) (@Transf_cat A C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U G Y) g)));
assertnot [R L : Cat] (F : τ (Functor R L)) (G : τ (Functor L R)) (J : τ (@Adjunction R L F G)) (x : τ (Obj R)) (y : τ
  (Obj L)) (h k : τ (Obj (Hom_cat L (@fapp0 R L F x) y))) ⊢ @eq_refl (Obj (Hom_cat R x (@fapp0 L R G y))) (@fapp0
  (Hom_cat L (@fapp0 R L F x) y) (Hom_cat R x (@fapp0 L R G y)) (@adjunction_transpose_func R L F G J x y) h) : τ (@=
  (Obj (Hom_cat R x (@fapp0 L R G y))) (@fapp0 (Hom_cat L (@fapp0 R L F x) y) (Hom_cat R x (@fapp0 L R G y))
  (@adjunction_transpose_func R L F G J x y) h) (@fapp0 (Hom_cat L (@fapp0 R L F x) y) (Hom_cat R x (@fapp0 L R G y))
  (@adjunction_transpose_func R L F G J x y) k));
assertnot [R L : Cat] (F : τ (Functor R L)) (G : τ (Functor L R)) (J : τ (@Adjunction R L F G)) (x : τ (Obj R)) (y : τ
  (Obj L)) (h k : τ (Obj (Hom_cat R x (@fapp0 L R G y)))) ⊢ @eq_refl (Obj (Hom_cat L (@fapp0 R L F x) y)) (@fapp0
  (Hom_cat R x (@fapp0 L R G y)) (Hom_cat L (@fapp0 R L F x) y) (@adjunction_untranspose_func R L F G J x y) h) : τ
  (@= (Obj (Hom_cat L (@fapp0 R L F x) y)) (@fapp0 (Hom_cat R x (@fapp0 L R G y)) (Hom_cat L (@fapp0 R L F x) y)
  (@adjunction_untranspose_func R L F G J x y) h) (@fapp0 (Hom_cat R x (@fapp0 L R G y)) (Hom_cat L (@fapp0 R L F x)
  y) (@adjunction_untranspose_func R L F G J x y) k));
assertnot [A B D C : Cat] (V : τ (Functor A B)) (U : τ (Functor B D)) (F F0 : τ (Functor D C)) ⊢ @eq_refl (Functor A
  C) (@hom_precomp_along_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) C A D (@comp_cat_fapp0 A B D U V) F) : τ (@=
  (Functor A C) (@hom_precomp_along_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) C A D (@comp_cat_fapp0 A B D U V) F)
  (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B D C F0 U) V));
assertnot [A B C : Cat] (Prod Prod0 : τ (Functor (Product_cat C C) C)) (U : τ (Functor A B)) (F G : τ (Functor B C)) ⊢
  @eq_refl (Functor A C) (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G)) U) : τ (@= (Functor A C) (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B
  (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) U) (@fapp0
  (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod0) (@Struct_sigma
  (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U))));
