/* Whole diagram transposition in an ordinary target.
   First exchange h:F⇒G, then introduce its arrow family in Functor_cat(B,C)
   and exchange the remaining walking-arrow and B arguments. This keeps
   every column and shape-arrow action in one internal functor term.
   C1 states the ordinary scope; no general lax/oplax interchange theorem
   or manually supplied naturality square is introduced. */
require open emdash.emdash3_2_arrow_diagram_families;

// i ↦ the whole B-family of arrows h(b)[i]:F(b)[i]→G(b)[i].
symbol one_cat_diagram_transpose_family_func
  [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G))
  : τ (Functor I (Functor_cat B (Functor_cat WalkingArrow_cat C)))
≔ @comp_cat_fapp0 I
    (Functor_cat WalkingArrow_cat (Functor_cat B C))
    (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@sym_func_func WalkingArrow_cat B C)
    (@transf_arrow_diagram_func I (Functor_cat B C)
      (@sym_func B I C F) (@sym_func B I C G)
      (@sym_func_func_transf B I C F G h));

// The column at i is an observation of the original whole family.
symbol one_cat_diagram_transpose_column_func
  [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G)) (i : τ (Obj I))
  : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @fapp0 I (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@one_cat_diagram_transpose_family_func B I C C1 F G h) i;

// Shape-arrow action is the same whole family Hom action; no equality transport.
symbol one_cat_diagram_transpose_transf
  [B I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat I C))]
  (h : τ (@Transf B (Functor_cat I C) F G))
  [i j : τ (Obj I)] (u : τ (Hom I i j))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C)
      (@one_cat_diagram_transpose_column_func B I C C1 F G h i)
      (@one_cat_diagram_transpose_column_func B I C C1 F G h j))
≔ @fapp1_fapp0 I (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@one_cat_diagram_transpose_family_func B I C C1 F G h) i j u;
