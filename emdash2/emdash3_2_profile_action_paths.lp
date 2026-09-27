/* Paths from semantic whole-action profiles; no runtime cuts or new axioms. */
require open emdash.emdash3_2_gray_profiles;
require open emdash.emdash3_2_one_cat_action_paths;

symbol profile_composition_path [A B : Cat] (F : τ (Functor A B))
 (PF : τ (@IsStrictFunctor A B F)) [x y z : τ (Obj A)]
 (g : τ (Hom A y z)) (f : τ (Hom A x y))
 : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
   (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f))
   (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B F y z g) (@fapp1_fapp0 A B F x y f)))
≔ @eq_trans _ _ _ _
   (@eq_ap (Hom A x z) (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
     (λ h : τ (Hom A x z), @fapp1_fapp0 A B F x z h)
     (@comp_fapp0 A x y z g f) (@hom_postcomp_fapp0 A A (@id_func A) x y z g f)
     (@comp_postcomp_path A x y z g f))
   (@eq_sym _ _ _
     (@strict_cell_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F z))
       (@strict_functor_compositor_lhs A B F x y z g f)
       (@strict_functor_compositor_rhs A B F x y z g f)
       (@fapp1_compositor A B F x y z g f)
       (@strict_functor_compositor_evidence A B F PF x y z g f)));

symbol profile_component_naturality_path [A B : Cat]
 [F G : τ (Functor A B)] (eta : τ (@Transf A B F G))
 (PE : τ (@IsStrictTransfor A B F G eta)) [x y : τ (Obj A)] (f : τ (Hom A x y))
 : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
   (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x eta))
   (@comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y eta) (@fapp1_fapp0 A B F x y f)))
≔ @eq_trans _ _ _ _
   (@strict_cell_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
     (@fapp0 (Hom_cat A x x) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)) (@strict_transfor_naturality_lhs_func A B F G eta x x y f) (@id A x))
     (@fapp0 (Hom_cat A x x) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)) (@strict_transfor_naturality_rhs_func A B F G eta x x y f) (@id A x))
     (@tapp1_post_laxity_cell A B F G eta x x y f (@id A x))
     (@strict_transfor_naturality_evidence A B F G eta PE x x y f (@id A x)))
   (@eq_sym _ _ _
     (@strict_cell_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
     (@fapp0 (Hom_cat A y y) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)) (@strict_transfor_pre_naturality_lhs_func A B F G eta y x y f) (@id A y))
     (@fapp0 (Hom_cat A y y) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y)) (@strict_transfor_pre_naturality_rhs_func A B F G eta y x y f) (@id A y))
       (@tapp1_pre_laxity_cell A B F G eta x y y f (@id A y))
       (@strict_transfor_pre_naturality_evidence A B F G eta PE x y y f (@id A y))));
