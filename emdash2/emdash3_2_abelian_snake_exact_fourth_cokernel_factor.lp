/* Descend the coextension through Coker(gamma). */

require open emdash.emdash3_2_abelian_snake_exact_fourth_gamma_zero;

symbol abelian_snake_fourth_gamma_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (@CokernelCoannihilator C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
      (@abelian_snake_gamma C P t Ab A B X D triple)
      (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
≔ @Struct_sigma
  (Hom C D (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
  (λ h : τ
    (Hom C D (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)), @=
    (Hom C
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
    (@comp_fapp0 C _ _ _ h (@abelian_snake_gamma C P t Ab A B X D triple))
    (@preadditive_hom_zero C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)))
  (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_y_gamma_zero_path C P t Ab A B X D T triple cocone);

symbol abelian_snake_fourth_cokernel_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (Hom C
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
≔ @computational_cokernel_colift C
  (@abelian_stability_preadditive C P t Ab)
  (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
  (@abelian_snake_gamma C P t Ab A B X D triple)
  (@abelian_snake_gamma_cokernel C P t Ab A B X D triple)
  (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_gamma_cocone C P t Ab A B X D T triple cocone);

symbol abelian_snake_fourth_cokernel_factor_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (@=
      (Hom C D (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_c_gamma C P t Ab A B X D triple))
      (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone))
≔ @computational_cokernel_colift_path C
  (@abelian_stability_preadditive C P t Ab)
  (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
  (@abelian_snake_gamma C P t Ab A B X D triple)
  (@abelian_snake_gamma_cokernel C P t Ab A B X D triple)
  (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_gamma_cocone C P t Ab A B X D T triple cocone);
