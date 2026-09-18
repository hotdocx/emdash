require open emdash.emdash3_2_one_cat_adjunction_introduction;
// catalog-area: Ordinary adjunction introduction from Hom comparison

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @eq_refl (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))
 : τ (@= (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) i);

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) ≡ i;

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (j : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @eq_refl (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))
 : τ (@= (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) j);

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @eq_refl (@ProfMap A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)))
 : τ (@= (@ProfMap A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @eq_refl (@ProfMap A B (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)))
 : τ (@= (@ProfMap A B (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) ⊢ @eq_refl (Functor (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b))) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b)
 : τ (@= (Functor (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b))) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) (f : τ (Obj (Hom_cat B (@fapp0 A B F a) b))) ⊢
 @eq_refl (Obj (Hom_cat A a (@fapp0 B A G b))) (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) f)
 : τ (@= (Obj (Hom_cat A a (@fapp0 B A G b))) (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) f) (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) f));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) ⊢ @eq_refl (Functor (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b)) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b)
 : τ (@= (Functor (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b)) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) (f : τ (Obj (Hom_cat A a (@fapp0 B A G b)))) ⊢
 @eq_refl (Obj (Hom_cat B (@fapp0 A B F a) b)) (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) f)
 : τ (@= (Obj (Hom_cat B (@fapp0 A B F a) b)) (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) f) (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) f));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) (f : τ (Obj (Hom_cat B (@fapp0 A B F a) b))) ⊢
 @fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) f) ≡ f;

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) ⊢
 @comp_cat_fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) ≡ @id_func (Hom_cat B (@fapp0 A B F a) b);

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) (f : τ (Obj (Hom_cat A a (@fapp0 B A G b)))) ⊢
 @fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) f) ≡ f;

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B)) ⊢
 @comp_cat_fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@adjunction_transpose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) (@adjunction_untranspose_func A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) a b) ≡ @id_func (Hom_cat A a (@fapp0 B A G b));

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (j : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @eq_refl (@ProfMap A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)))
 : τ (@= (@ProfMap A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) j));

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (j : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @eq_refl (@ProfMap A B (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)))
 : τ (@= (@ProfMap A B (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) j));

assert [A : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A)) (x y : τ (Obj A)) ⊢
 @eq_refl (Functor (Hom_cat A x y) (Hom_cat A x y)) (@adjunction_transpose_func A A (@id_func A) (@id_func A) (@one_cat_adjunction_from_hom_comparison A A A1 A1 (@id_func A) (@id_func A) (@defiso_refl (Prof_cat A A) (@Unit_prof A))) x y)
 : τ (@= (Functor (Hom_cat A x y) (Hom_cat A x y)) (@adjunction_transpose_func A A (@id_func A) (@id_func A) (@one_cat_adjunction_from_hom_comparison A A A1 A1 (@id_func A) (@id_func A) (@defiso_refl (Prof_cat A A) (@Unit_prof A))) x y) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Unit_prof A)
 (@Product_pair (Op_cat A) A x y) (@defiso_to (Prof_cat A A) (@Unit_prof A) (@Unit_prof A)
   (@defiso_refl (Prof_cat A A) (@Unit_prof A)))));

assertnot [A : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A)) (x y : τ (Obj A)) ⊢
 (@adjunction_transpose_func A A (@id_func A) (@id_func A) (@one_cat_adjunction_from_hom_comparison A A A1 A1 (@id_func A) (@id_func A) (@defiso_refl (Prof_cat A A) (@Unit_prof A))) x y) ≡ (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Unit_prof A)
 (@Product_pair (Op_cat A) A x y) (@defiso_to (Prof_cat A A) (@Unit_prof A) (@Unit_prof A)
   (@defiso_refl (Prof_cat A A) (@Unit_prof A))));

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) ≡ (@one_cat_hom_comparison_unit A B A1 B1 F G i);

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) ≡ (@one_cat_hom_comparison_counit A B A1 B1 F G i);

assert [K A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (M : τ (Functor K A)) (N : τ (Functor K B)) (alpha : τ (Obj (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N))) ⊢
 @fapp0 (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)) (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N) (@one_cat_adjunction_family_untranspose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N) (@fapp0 (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N) (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)) (@one_cat_adjunction_family_transpose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N) alpha) ≡ alpha;

assert [K A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (M : τ (Functor K A)) (N : τ (Functor K B)) ⊢ @comp_cat_fapp0 (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N) (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)) (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N) (@one_cat_adjunction_family_untranspose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N) (@one_cat_adjunction_family_transpose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N)
 ≡ @id_func (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N);

assert [K A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (M : τ (Functor K A)) (N : τ (Functor K B)) (alpha : τ (Obj (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)))) ⊢
 @fapp0 (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N) (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)) (@one_cat_adjunction_family_transpose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N) (@fapp0 (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)) (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N) (@one_cat_adjunction_family_untranspose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N) alpha) ≡ alpha;

assert [K A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (M : τ (Functor K A)) (N : τ (Functor K B)) ⊢ @comp_cat_fapp0 (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)) (Hom_cat (Functor_cat K B) (@fapp0 _ _ (@comp_cat_cov_func K A B F) M) N) (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N)) (@one_cat_adjunction_family_transpose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N) (@one_cat_adjunction_family_untranspose_func K A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) M N)
 ≡ @id_func (Hom_cat (Functor_cat K A) M (@fapp0 _ _ (@comp_cat_cov_func K B A G) N));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x x1 : τ (Obj A)) (y : τ (Obj B))
 (f : τ (Hom B (@fapp0 A B F x1) y)) (g : τ (Hom A x x1)) ⊢
 @comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F x1))) y
   (@tapp1_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) (@fapp0 A B F x1) y (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) f)
   (@fapp1_fapp0 A B F x (@fapp0 B A G (@fapp0 A B F x1))
     (@tapp1_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x x1 (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) g))
 ≡ @comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F x1) y f (@fapp1_fapp0 A B F x x1 g);

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj A)) (y1 y : τ (Obj B))
 (f : τ (Hom A x (@fapp0 B A G y1))) (g : τ (Hom B y1 y)) ⊢
 @comp_fapp0 A x (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G y1))) (@fapp0 B A G y)
   (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G y1)) y
     (@tapp1_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) y1 y (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) g))
   (@tapp1_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@fapp0 B A G y1) (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) f)
 ≡ @comp_fapp0 A x (@fapp0 B A G y1) (@fapp0 B A G y) (@fapp1_fapp0 B A G y1 y g) f;

// An unrelated native adjunction receives no agreement with an arbitrary input.
assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (J : τ (@Adjunction A B F G))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @eq_refl (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G J)
 : τ (@= (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G J) i);
assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢
 @one_cat_adjunction_from_hom_comparison_unit_modification A B A1 B1 F G i : τ (Hom (@Transf_cat A A (@id_func A) (@comp_cat_fapp0 A B A G F)) (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_unit A B A1 B1 F G i));
assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢
 @one_cat_adjunction_from_hom_comparison_unit_path A B A1 B1 F G i : τ (@= (@Transf A A (@id_func A) (@comp_cat_fapp0 A B A G F)) (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_unit A B A1 B1 F G i));
assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢
 @one_cat_adjunction_from_hom_comparison_counit_modification A B A1 B1 F G i : τ (Hom (@Transf_cat B B (@comp_cat_fapp0 B A B F G) (@id_func B)) (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_counit A B A1 B1 F G i));
assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢
 @one_cat_adjunction_from_hom_comparison_counit_path A B A1 B1 F G i : τ (@= (@Transf B B (@comp_cat_fapp0 B A B F G) (@id_func B)) (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_counit A B A1 B1 F G i));

// A supplied comparison may itself be a native adjunction projection.
assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A)) (J : τ (@Adjunction A B F G)) ⊢
 @one_cat_adjunction_from_hom_comparison_input_path A B A1 B1 F G (@Adjunction_hom_prof_comparison A B F G J)
 : τ (@= (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))
   (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G (@Adjunction_hom_prof_comparison A B F G J)))
   (@Adjunction_hom_prof_comparison A B F G J));
assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A)) (J : τ (@Adjunction A B F G)) ⊢ @eq_refl (@ProfMap A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G (@Adjunction_hom_prof_comparison A B F G J))))
 : τ (@= (@ProfMap A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G (@Adjunction_hom_prof_comparison A B F G J)))) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G J)));
assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A)) (J : τ (@Adjunction A B F G)) ⊢ @eq_refl (@ProfMap A B (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G (@Adjunction_hom_prof_comparison A B F G J))))
 : τ (@= (@ProfMap A B (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G (@Adjunction_hom_prof_comparison A B F G J)))) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Adjunction_hom_prof_comparison A B F G J)));
