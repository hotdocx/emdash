/* Generic evaluation, components, mixed action and retained next Hom. */
require open emdash.emdash3_2_diagram_evaluation;

assert (I C : Cat) (i : τ (Obj I)) (F : τ (Functor I C))
  ⊢ @fapp0 (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F
    ≡ @fapp0 I C F i;

assert (I C : Cat) (i j : τ (Obj I)) (u : τ (Hom I i j))
  (F : τ (Functor I C))
  ⊢ @tapp0_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
      F (@diagram_evaluation_transf I C i j u)
    ≡ @fapp1_fapp0 I C F i j u;

assert (I C : Cat) (i j : τ (Obj I))
  ⊢ @fapp1_func I (Functor_cat (Functor_cat I C) C)
      (@diagram_evaluation_func I C) i j
  : τ (Functor (Hom_cat I i j)
      (@Transf_cat (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)));

assert (I C : Cat) (i : τ (Obj I))
  (F G : τ (Functor I C)) (eta : τ (@Transf I C F G))
  ⊢ @fapp1_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) F G eta
    ≡ @tapp0_fapp0 I C F G i eta;

assert (I C : Cat) (i j : τ (Obj I)) (u : τ (Hom I i j))
  (F G : τ (Functor I C)) (eta : τ (@Transf I C F G))
  ⊢ @tapp1_fapp0 (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
      F G (@diagram_evaluation_transf I C i j u) eta
    ≡ @tapp1_fapp0 I C F G i j eta u;

// The mixed operation remains a whole functor; its next hom action is typed
// over the actual off-diagonal components, not a capped raw function.
assert (I C : Cat) (i j : τ (Obj I)) (u : τ (Hom I i j))
  (F G : τ (Functor I C)) (eta theta : τ (@Transf I C F G))
  ⊢ @fapp1_func
      (@Transf_cat I C F G)
      (Hom_cat C (@fapp0 I C F i) (@fapp0 I C G j))
      (@tapp1_func (Functor_cat I C) C
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j)
        F G (@diagram_evaluation_transf I C i j u))
      eta theta
    : τ (Functor
      (Hom_cat (@Transf_cat I C F G) eta theta)
      (Hom_cat (Hom_cat C (@fapp0 I C F i) (@fapp0 I C G j))
        (@tapp1_fapp0 I C F G i j eta u)
        (@tapp1_fapp0 I C F G i j theta u)));

assertnot (I C : Cat) (i : τ (Obj I))
  (F : τ (Functor I C)) (other : τ (Obj C))
  ⊢ @fapp0 (Functor_cat I C) C (@diagram_evaluation_at_func I C i) F ≡ other;

assert [B I C : Cat] (i : τ (Obj I))
  (F : τ (Functor B (Functor_cat I C)))
  ⊢ @fapp0 _ _ (@diagram_family_evaluation_func B I C i) F
    ≡ @sym_fapp0_func B I C F i;
assert [B I C : Cat] (i : τ (Obj I))
  (F G : τ (Functor B (Functor_cat I C)))
  (h : τ (@Transf B (Functor_cat I C) F G))
  ⊢ @fapp1_fapp0 _ _ (@diagram_family_evaluation_func B I C i) F G h
    ≡ @sym_transf_tapp0_transf B I C F G h i;

// Whole family proof-time comparisons retain all relevant data.
assert (A B I C : Cat) (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat I C))) (F : τ (Functor A
  B)) (i j : τ (Obj I)) (u v : τ (Hom I i
    j))
  ⊢ eq_refl (@diagram_family_transf A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i j u) : τ (@= (@Transf A C
    (@comp_cat_fapp0 A B C (@diagram_family_at_func B I C D i) F) (@comp_cat_fapp0 A B C (@diagram_family_at_func B I
    C D j) F)) (@diagram_family_transf A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i j u) (@fapp0 _ _
    (@comp_cat_con_fapp1_func A B C F (@diagram_family_at_func B I C D i) (@diagram_family_at_func B I C D j))
    (@diagram_family_transf B I C D i j u)));

assertnot (A B I C : Cat) (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat I C))) (F : τ
  (Functor A B)) (i j : τ (Obj I)) (u v : τ (Hom
    I i j))
  ⊢ eq_refl (@diagram_family_transf A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i j u) : τ (@= (@Transf A C
    (@comp_cat_fapp0 A B C (@diagram_family_at_func B I C D i) F) (@comp_cat_fapp0 A B C (@diagram_family_at_func B I
    C D j) F)) (@diagram_family_transf A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i j u) (@fapp0 _ _
    (@comp_cat_con_fapp1_func A B C F (@diagram_family_at_func B I C D i) (@diagram_family_at_func B I C D j))
    (@diagram_family_transf B I C D i j v)));

assert (B I C : Cat) (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat I C))) (i j : τ (Obj I))
  (u v : τ (Hom I i j))
  ⊢ eq_refl (@diagram_family_transf B I C D i j u) : τ (@= (@Transf B C (@diagram_family_at_func B I C D i)
    (@diagram_family_at_func B I C D j)) (@diagram_family_transf B I C D i j u) (@fapp0 _ _ (@comp_cat_con_fapp1_func
    B (Functor_cat I C) C D (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j))
    (@diagram_evaluation_transf I C i j u)));

assertnot (B I C : Cat) (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat I C))) (i j : τ (Obj
  I)) (u v : τ (Hom I i j))
  ⊢ eq_refl (@diagram_family_transf B I C D i j u) : τ (@= (@Transf B C (@diagram_family_at_func B I C D i)
    (@diagram_family_at_func B I C D j)) (@diagram_family_transf B I C D i j u) (@fapp0 _ _ (@comp_cat_con_fapp1_func
    B (Functor_cat I C) C D (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j))
    (@diagram_evaluation_transf I C i j v)));
