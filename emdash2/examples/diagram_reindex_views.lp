/* Accumulated evaluator comparison retains all data and every runtime owner. */
require open emdash.emdash3_2_diagram_reindex_views;

assert [A B I C : Cat] (F : τ (Functor A (Functor_cat I C))) (D : τ (Functor B A)) (i : τ (Obj I))
  ⊢ @eq_refl (Functor B C)
      (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F) D)
    : τ (@= (Functor B C)
      (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F) D)
      (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C F i) D));
assertnot [A B I C : Cat] (F F2 : τ (Functor A (Functor_cat I C))) (D : τ (Functor B A)) (i : τ (Obj I))
  ⊢ @eq_refl (Functor B C)
      (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F) D)
    : τ (@= (Functor B C)
      (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F) D)
      (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C F2 i) D));

assertnot [A B I C : Cat] (F : τ (Functor A (Functor_cat I C))) (D : τ (Functor B A)) (i : τ (Obj I)) (D2 : τ (Functor
  B A))
  ⊢ (@eq_refl (Functor B C) (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func
    I C i) F) D)) : τ (@= (Functor B C) (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C
    (@diagram_evaluation_at_func I C i) F) D) (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C F i) D2));

assertnot [A B I C : Cat] (F : τ (Functor A (Functor_cat I C))) (D : τ (Functor B A)) (i : τ (Obj I)) (i2 : τ (Obj I))
  ⊢ (@eq_refl (Functor B C) (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func
    I C i) F) D)) : τ (@= (Functor B C) (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C
    (@diagram_evaluation_at_func I C i) F) D) (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C F i2) D));

assertnot [A B I C : Cat] (F : τ (Functor A (Functor_cat I C))) (D : τ (Functor B A)) (i : τ (Obj I))
  ⊢ (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F) D) ≡
    (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C F i) D);

assert [A B I C : Cat] (F : τ (Functor A (Functor_cat I C))) (D : τ (Functor B A)) (i : τ (Obj I)) (x : τ (Obj B))
  ⊢ (@fapp0 B C (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F)
    D) x) ≡ (@fapp0 B C (@comp_cat_fapp0 B A C (@diagram_family_at_func A I C F i) D) x);

assert [A B I C : Cat] (F : τ (Functor A (Functor_cat I C))) (D : τ (Functor B A)) (i : τ (Obj I)) (x y : τ (Obj B))
  ⊢ (@fapp1_func B C (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i)
    F) D) x y) : τ (Functor (Hom_cat B x y) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A
    (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F) D) x) (@fapp0 B C (@comp_cat_fapp0 B A C
    (@comp_cat_fapp0 A (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F) D) y)));
