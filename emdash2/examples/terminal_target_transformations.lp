/* Transformations and all higher cells into the terminal category.
   Keep arbitrary source categories and independently supplied functors. */
require open emdash.emdash3_2_one_cat_adjunction_families;
// catalog-area: Categorical contraction and ordinary terminal adjunctions

assert [B : Cat] (F G : τ (Functor B Terminal_cat)) ⊢
  @Transf_cat B Terminal_cat F G ≡ Terminal_cat;

assert [B : Cat] (F G : τ (Functor B Terminal_cat)) ⊢
  Hom_cat (Functor_cat B Terminal_cat) F G ≡ Terminal_cat;

assert [B : Cat] (F G : τ (Functor B Terminal_cat))
  (h k : τ (@Transf B Terminal_cat F G)) ⊢
  Hom_cat (@Transf_cat B Terminal_cat F G) h k ≡ Terminal_cat;

// The literal terminal target is essential; arbitrary targets do not collapse.
assertnot [B C : Cat] (F G : τ (Functor B C)) ⊢
  @Transf_cat B C F G ≡ Terminal_cat;

// Actual lifted terminal universality now has a terminal comparison domain.
// This retains native postcomposition endpoints, with no extra comparison rule.
symbol review_terminal_family_iso [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T1 : τ (IsNCat (cat_succ cat_zero) Terminal_cat))
  [t : τ (Obj C)]
  (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t)))
  (F : τ (Functor B C)) (V : τ (Functor B Terminal_cat))
  : τ (@DefIso Cat_cat Terminal_cat
      (Hom_cat (Functor_cat B C) F
        (@fapp0 _ _ (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t)) V)))
≔ @adjunction_hom_component_iso (Functor_cat B C) (Functor_cat B Terminal_cat)
    (@comp_cat_cov_func B C Terminal_cat (Terminal_func C))
    (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t))
    (@one_cat_postcomp_adjunction B C Terminal_cat C1 T1
      (Terminal_func C) (@Obj_func C t) J) F V;

// Both directions of the actual whole Hom comparison cancel.
assert [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T1 : τ (IsNCat (cat_succ cat_zero) Terminal_cat)) [t : τ (Obj C)]
  (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t)))
  (F : τ (Functor B C)) (V : τ (Functor B Terminal_cat)) ⊢
  @comp_cat_fapp0 _ _ _
    (@defiso_from _ _ _ (@review_terminal_family_iso B C C1 T1 t J F V))
    (@defiso_to _ _ _ (@review_terminal_family_iso B C C1 T1 t J F V))
  ≡ @id_func Terminal_cat;

assert [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T1 : τ (IsNCat (cat_succ cat_zero) Terminal_cat)) [t : τ (Obj C)]
  (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t)))
  (F : τ (Functor B C)) (V : τ (Functor B Terminal_cat)) ⊢
  @comp_cat_fapp0 _ _ _
    (@defiso_to _ _ _ (@review_terminal_family_iso B C C1 T1 t J F V))
    (@defiso_from _ _ _ (@review_terminal_family_iso B C C1 T1 t J F V))
  ≡ @id_func (Hom_cat (Functor_cat B C) F
      (@fapp0 _ _ (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t)) V));

// The direct initial adjunction uses the same terminal-target computation.
symbol review_initial_family_iso [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T1 : τ (IsNCat (cat_succ cat_zero) Terminal_cat)) [t : τ (Obj C)]
  (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C)))
  (F : τ (Functor B C)) (V : τ (Functor B Terminal_cat))
  : τ (@DefIso Cat_cat
      (Hom_cat (Functor_cat B C)
        (@fapp0 _ _ (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t)) V) F)
      Terminal_cat)
≔ @adjunction_hom_component_iso (Functor_cat B Terminal_cat) (Functor_cat B C)
    (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t))
    (@comp_cat_cov_func B C Terminal_cat (Terminal_func C))
    (@one_cat_postcomp_adjunction B Terminal_cat C T1 C1
      (@Obj_func C t) (Terminal_func C) J) V F;

assert [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T1 : τ (IsNCat (cat_succ cat_zero) Terminal_cat)) [t : τ (Obj C)]
  (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C)))
  (F : τ (Functor B C)) (V : τ (Functor B Terminal_cat)) ⊢
  @comp_cat_fapp0 _ _ _
    (@defiso_to _ _ _ (@review_initial_family_iso B C C1 T1 t J F V))
    (@defiso_from _ _ _ (@review_initial_family_iso B C C1 T1 t J F V))
  ≡ @id_func Terminal_cat;

assert [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T1 : τ (IsNCat (cat_succ cat_zero) Terminal_cat)) [t : τ (Obj C)]
  (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C)))
  (F : τ (Functor B C)) (V : τ (Functor B Terminal_cat)) ⊢
  @comp_cat_fapp0 _ _ _
    (@defiso_from _ _ _ (@review_initial_family_iso B C C1 T1 t J F V))
    (@defiso_to _ _ _ (@review_initial_family_iso B C C1 T1 t J F V))
  ≡ @id_func (Hom_cat (Functor_cat B C)
      (@fapp0 _ _ (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t)) V) F);
