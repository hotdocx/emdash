require open emdash.emdash3_2_one_cat_hom_comparison_data;
// catalog-area: Ordinary Hom comparison identity images

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @one_cat_hom_comparison_unit A B A1 B1 F G i
 : τ (@Transf A A (@id_func A) (@comp_cat_fapp0 A B A G F));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x y : τ (Obj A)) ⊢
 @tapp1_func A A (@id_func A) (@comp_cat_fapp0 A B A G F) x y (@one_cat_hom_comparison_unit A B A1 B1 F G i)
 : τ (Functor (Hom_cat A x y)
     (Hom_cat A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) y)));

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj A)) (p : τ (Hom A x x)) ⊢
 @tapp1_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x x (@one_cat_hom_comparison_unit A B A1 B1 F G i) p
 ≡ @tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@one_cat_hom_comparison_unit A B A1 B1 F G i);

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj A)) ⊢
 @one_cat_hom_comparison_unit_component_path A B A1 B1 F G i x : τ (@= (Hom A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) x)) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@one_cat_hom_comparison_unit A B A1 B1 F G i)) (@fapp0 _ _ (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B x (@fapp0 A B F x)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F x))));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @one_cat_hom_comparison_counit A B A1 B1 F G i
 : τ (@Transf B B (@comp_cat_fapp0 B A B F G) (@id_func B));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x y : τ (Obj B)) ⊢
 @tapp1_func B B (@comp_cat_fapp0 B A B F G) (@id_func B) x y (@one_cat_hom_comparison_counit A B A1 B1 F G i)
 : τ (Functor (Hom_cat B x y)
     (Hom_cat B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) y)));

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj B)) (p : τ (Hom B x x)) ⊢
 @tapp1_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x x (@one_cat_hom_comparison_counit A B A1 B1 F G i) p
 ≡ @tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@one_cat_hom_comparison_counit A B A1 B1 F G i);

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj B)) ⊢
 @one_cat_hom_comparison_counit_component_path A B A1 B1 F G i x : τ (@= (Hom B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) x)) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@one_cat_hom_comparison_counit A B A1 B1 F G i)) (@fapp0 _ _ (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G x) x) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G x))));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @one_cat_hom_comparison_triangle_left_modification A B A1 B1 F G i : τ (Hom (@Transf_cat A B F F) (@one_cat_hom_comparison_triangle_left_transf A B A1 B1 F G i) (@id (Functor_cat A B) F));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @one_cat_hom_comparison_triangle_left_path A B A1 B1 F G i : τ (@= (@Transf A B F F) (@one_cat_hom_comparison_triangle_left_transf A B A1 B1 F G i) (@id (Functor_cat A B) F));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @one_cat_hom_comparison_triangle_right_modification A B A1 B1 F G i : τ (Hom (@Transf_cat B A G G) (@one_cat_hom_comparison_triangle_right_transf A B A1 B1 F G i) (@id (Functor_cat B A) G));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢ @one_cat_hom_comparison_triangle_right_path A B A1 B1 F G i : τ (@= (@Transf B A G G) (@one_cat_hom_comparison_triangle_right_transf A B A1 B1 F G i) (@id (Functor_cat B A) G));

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x y : τ (Obj A)) (f : τ (Hom A x y)) ⊢
 @one_cat_profmap_reconstruction_action_path A A A1 A1 (@id_func A) (@comp_cat_fapp0 A B A G F) (@hom_comparison_unit_profmap A B F G i) x y f
 : τ (@= (Obj (Hom_cat A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) y))) (@tapp1_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x y (@one_cat_hom_comparison_unit A B A1 B1 F G i) f) (@fapp0 (Hom_cat A x y) (Hom_cat A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) y)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A A (@id_func A) (@comp_cat_fapp0 A B A G F)) (@Product_pair (Op_cat A) A x y) (@hom_comparison_unit_profmap A B F G i)) f));

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i j : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢
 @one_cat_hom_comparison_unit A B A1 B1 F G i ≡ @one_cat_hom_comparison_unit A B A1 B1 F G j;

assert [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x y : τ (Obj B)) (f : τ (Hom B x y)) ⊢
 @one_cat_profmap_reconstruction_action_path B B B1 B1 (@comp_cat_fapp0 B A B F G) (@id_func B) (@hom_comparison_counit_profmap A B F G i) x y f
 : τ (@= (Obj (Hom_cat B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) y))) (@tapp1_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x y (@one_cat_hom_comparison_counit A B A1 B1 F G i) f) (@fapp0 (Hom_cat B x y) (Hom_cat B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) y)) (@tapp0_fapp0 (Product_cat (Op_cat B) B) Cat_cat (@Unit_prof B) (@Hom_prof_along B B B (@comp_cat_fapp0 B A B F G) (@id_func B)) (@Product_pair (Op_cat B) B x y) (@hom_comparison_counit_profmap A B F G i)) f));

assertnot [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i j : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) ⊢
 @one_cat_hom_comparison_counit A B A1 B1 F G i ≡ @one_cat_hom_comparison_counit A B A1 B1 F G j;
