/* Whole ordinary-target transposition retains the original diagram map. */
require open emdash.emdash3_2_one_cat_diagram_transpose;

// Typed proof-time comparison after exchange, with the original h[i].
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  ⊢ @eq_refl (Functor B (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_transpose_column_func B I C C1 F G h i)
    : τ (@= (Functor B (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_transpose_column_func B I C C1 F G h i)
      (@transf_arrow_diagram_func B C
        (@diagram_family_at_func B I C F i) (@diagram_family_at_func B I C G i)
        (@sym_transf_tapp0_transf B I C F G h i)));

// The src of the whole column is the original evaluated diagram family.
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  ⊢ @diagram_family_at_func B WalkingArrow_cat C (@one_cat_diagram_transpose_column_func B I C C1 F G h i) walking_arrow_src
    ≡ @diagram_family_at_func B I C F i;

// The tgt of the whole column is the original evaluated diagram family.
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  ⊢ @diagram_family_at_func B WalkingArrow_cat C (@one_cat_diagram_transpose_column_func B I C C1 F G h i) walking_arrow_tgt
    ≡ @diagram_family_at_func B I C G i;

// The whole column differential is the original evaluated transformation.
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  ⊢ @diagram_family_transf B WalkingArrow_cat C (@one_cat_diagram_transpose_column_func B I C C1 F G h i)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator
    ≡ @sym_transf_tapp0_transf B I C F G h i;

// A nonidentity shape arrow retains the F side at every parameter.
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) [i j : τ (Obj I)] (u : τ (Hom I i j)) (x : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_transpose_column_func B I C C1 F G h i) (@one_cat_diagram_transpose_column_func B I C C1 F G h j) x (@one_cat_diagram_transpose_transf B I C C1 F G h i j u))
    ≡ @fapp1_fapp0 I C (@fapp0 B (Functor_cat I C) F x) i j u;

// A nonidentity shape arrow retains the G side at every parameter.
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) [i j : τ (Obj I)] (u : τ (Hom I i j)) (x : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_transpose_column_func B I C C1 F G h i) (@one_cat_diagram_transpose_column_func B I C C1 F G h j) x (@one_cat_diagram_transpose_transf B I C C1 F G h i j u))
    ≡ @fapp1_fapp0 I C (@fapp0 B (Functor_cat I C) G x) i j u;

// The next shape Hom remains the original whole functor's action.
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) [i j : τ (Obj I)] (u v : τ (Hom I i j))
  ⊢ @fapp1_func _ _ (@fapp1_func I (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_transpose_family_func B I C C1 F G h) i j) u v
    : τ (Functor (Hom_cat (Hom_cat I i j) u v)
      (Hom_cat (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_transpose_column_func B I C C1 F G h i) (@one_cat_diagram_transpose_column_func B I C C1 F G h j)) (@one_cat_diagram_transpose_transf B I C C1 F G h i j u) (@one_cat_diagram_transpose_transf B I C C1 F G h i j v)));

// The parameter Hom action remains available on the whole transposed map.
assert [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) [i j : τ (Obj I)] (u : τ (Hom I i j)) (x y : τ (Obj B))
  ⊢ @tapp1_func B (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_transpose_column_func B I C C1 F G h i) (@one_cat_diagram_transpose_column_func B I C C1 F G h j) x y (@one_cat_diagram_transpose_transf B I C C1 F G h i j u)
    : τ (Functor (Hom_cat B x y)
      (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_transpose_column_func B I C C1 F G h i) x) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_transpose_column_func B I C C1 F G h j) y)));

// The point comparison retains the chosen h, not an unrelated transformation.
assertnot [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (k : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  ⊢ @eq_refl (Functor B (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_transpose_column_func B I C C1 F G h i)
    : τ (@= (Functor B (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_transpose_column_func B I C C1 F G h i)
      (@transf_arrow_diagram_func B C
        (@diagram_family_at_func B I C F i) (@diagram_family_at_func B I C G i)
        (@sym_transf_tapp0_transf B I C F G k i)));
