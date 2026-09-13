/* Reviewer for whole evaluation computation and proof-time views. */
require open emdash.emdash3_2_diagram_evaluation;

// Evaluation after precomposition retains the remaining whole functor.
assert [B I C : Cat] [A : Cat] (D : τ (Functor B (Functor_cat I C)))
  (F : τ (Functor A B)) (i : τ (Obj I))
  ⊢ @diagram_family_at_func A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i
    ≡ @comp_cat_fapp0 A B C (@diagram_family_at_func B I C D i) F;

// Its whole Hom action agrees before selecting an arrow.
assert [B I C : Cat] [A : Cat] (D : τ (Functor B (Functor_cat I C)))
  (F : τ (Functor A B)) (i : τ (Obj I)) (x y : τ (Obj A))
  ⊢ @fapp1_func A C
      (@diagram_family_at_func A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i) x y
    ≡ @fapp1_func A C
      (@comp_cat_fapp0 A B C (@diagram_family_at_func B I C D i) F) x y;

// Typed proof-time reviewer: exact whole functor evaluation.
assert [B I C : Cat] (F : τ (Functor B (Functor_cat I C))) (i : τ (Obj I))
  ⊢ @eq_refl (Functor B C) (@diagram_family_at_func B I C F i)
    : τ (@= (Functor B C) (@diagram_family_at_func B I C F i)
      (@comp_cat_fapp0 B (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F));

// Typed proof-time reviewer: exact whole transformation evaluation.
assert [B I C : Cat] [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  ⊢ @eq_refl (@Transf B C
      (@comp_cat_fapp0 B (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F)
      (@comp_cat_fapp0 B (Functor_cat I C) C (@diagram_evaluation_at_func I C i) G))
      (@sym_transf_tapp0_transf B I C F G h i)
    : τ (@= (@Transf B C
      (@comp_cat_fapp0 B (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F)
      (@comp_cat_fapp0 B (Functor_cat I C) C (@diagram_evaluation_at_func I C i) G))
      (@sym_transf_tapp0_transf B I C F G h i)
      (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) F G) h));

// The transformation view computes the original component at every parameter.
assert [B I C : Cat] [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I)) (x : τ (Obj B))
  ⊢ @tapp0_fapp0 B C _ _ x (@sym_transf_tapp0_transf B I C F G h i)
    ≡ @tapp0_fapp0 I C _ _ i (@tapp0_fapp0 B (Functor_cat I C) F G x h);

// The comparison does not identify evaluations at unrelated shape points.
assertnot [B I C : Cat] (F : τ (Functor B (Functor_cat I C))) (i j : τ (Obj I))
  ⊢ @eq_refl (Functor B C) (@diagram_family_at_func B I C F i)
    : τ (@= (Functor B C) (@diagram_family_at_func B I C F i)
      (@comp_cat_fapp0 B (Functor_cat I C) C (@diagram_evaluation_at_func I C j) F));

// Nor does it identify unrelated input transformations.
assertnot [B I C : Cat] [F G : τ (Functor B (Functor_cat I C))]
  (h k : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  ⊢ @eq_refl (@Transf B C (@diagram_family_at_func B I C F i) (@diagram_family_at_func B I C G i))
      (@sym_transf_tapp0_transf B I C F G h i)
    : τ (@= (@Transf B C (@diagram_family_at_func B I C F i) (@diagram_family_at_func B I C G i))
      (@sym_transf_tapp0_transf B I C F G h i)
      (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) F G) k));

// The raw product-swap critical-pair schema is not diagram-valued.
assertnot [A B I C : Cat] (i : τ (Obj I))
  ⊢ @sym_fapp0_func (Product_cat A B) I C
      (@comp_cat_fapp0 (Product_cat A B) (Product_cat B A) (Product_cat A B)
        (@Product_swap_func B A) (@Product_swap_func A B)) i
    : τ (Functor (Product_cat A B) C);

// The raw product-map critical-pair schema has the same codomain mismatch.
assertnot [A0 A1 A2 B0 B1 B2 I C : Cat]
  (F01 : τ (Functor A0 A1)) (F12 : τ (Functor A1 A2))
  (G01 : τ (Functor B0 B1)) (G12 : τ (Functor B1 B2)) (i : τ (Obj I))
  ⊢ @sym_fapp0_func (Product_cat A0 B0) I C
      (@comp_cat_fapp0 (Product_cat A0 B0) (Product_cat A1 B1) (Product_cat A2 B2)
        (@Product_map_func A1 A2 B1 B2 F12 G12)
        (@Product_map_func A0 A1 B0 B1 F01 G01)) i
    : τ (Functor (Product_cat A0 B0) C);

// Compare evaluation before and after projecting its Hom owner.
assert [A B I C : Cat] (D : τ (Functor B (Functor_cat I C)))
  (F : τ (Functor A B)) (i : τ (Obj I)) (x y : τ (Obj A))
  ⊢ @sym_fapp0_fapp1_func A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i x y
    ≡ @fapp1_func A C
      (@comp_cat_fapp0 A B C (@sym_fapp0_func B I C D i) F) x y;

// Capped evaluation also joins the preprojected and whole routes.
assert [A B I C : Cat] (D : τ (Functor B (Functor_cat I C)))
  (F : τ (Functor A B)) (i : τ (Obj I)) (x y : τ (Obj A)) (p : τ (Hom A x y))
  ⊢ @fapp0 _ _
      (@sym_fapp0_fapp1_func A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i x y) p
    ≡ @fapp1_fapp0 A C
      (@comp_cat_fapp0 A B C (@sym_fapp0_func B I C D i) F) x y p;

// A further Hom of that same preprojected owner also joins.
assert [A B I C : Cat] (D : τ (Functor B (Functor_cat I C)))
  (F : τ (Functor A B)) (i : τ (Obj I)) (x y : τ (Obj A)) (p q : τ (Hom A x y))
  ⊢ @fapp1_func _ _
      (@sym_fapp0_fapp1_func A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i x y) p q
    ≡ @fapp1_func _ _
      (@fapp1_func A C (@comp_cat_fapp0 A B C (@sym_fapp0_func B I C D i) F) x y) p q;
