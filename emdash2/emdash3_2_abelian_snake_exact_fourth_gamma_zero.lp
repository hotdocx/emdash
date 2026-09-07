/* The lambda-coextension kills gamma by epic epsilon cancellation. */

require open emdash.emdash3_2_abelian_snake_exact_fourth_extension_projections;

symbol abelian_snake_fourth_psi_cbeta_beta_zero_path
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
      (Hom C B T)
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@cokernel_coannihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
          (@abelian_snake_c_beta C P t Ab A B X D triple))
        (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple))
      (@preadditive_hom_zero C (@abelian_stability_preadditive C P t Ab) B T))
≔ @eq_trans _ _ _ _
  (@eq_sym _ _ _
    (@comp_assoc C _ _ _ _
      (@cokernel_coannihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
      (@abelian_snake_c_beta C P t Ab A B X D triple)
      (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple)))
  (@preadditive_postcompose_zero_path C
    (@abelian_stability_preadditive C P t Ab) B
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple) T
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_c_beta C P t Ab A B X D triple)
      (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple))
    (@abelian_snake_c_beta_beta_zero_path C P t Ab A B X D triple));

symbol abelian_snake_fourth_y_gamma_epsilon_zero_path
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
      (Hom C B (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone)
          (@abelian_snake_gamma C P t Ab A B X D triple))
        (@abelian_snake_epsilon C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab) B
        (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)))
≔
  (@eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C B D)
        (Hom C B (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
        (λ h : τ
          (Hom C B D),
          (@comp_fapp0 C _ _ _
            (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone) h))
        _ _
        (@abelian_snake_gamma_path C P t Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone)
          (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C X (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
            (Hom C B (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
            (λ h : τ
              (Hom C X (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)),
              (@comp_fapp0 C _ _ _ h
                (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple)))
            _ _
            (@eq_sym _ _ _ (@abelian_snake_fourth_extension_path C P t Ab A B X D T triple cocone)))
          (@eq_trans _ _ _ _
            (@eq_sym _ _ _
              (@comp_assoc C _ _ _ _
                (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
                (@comp_fapp0 C _ _ _
                  (@cokernel_coannihilator_arrow C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
                    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
                  (@abelian_snake_c_beta C P t Ab A B X D triple))
                (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple)))
            (@preadditive_postcompose_zero_path C
              (@abelian_stability_preadditive C P t Ab) B T
              (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)
              (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
              (@comp_fapp0 C _ _ _
                (@comp_fapp0 C _ _ _
                  (@cokernel_coannihilator_arrow C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
                    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
                  (@abelian_snake_c_beta C P t Ab A B X D triple))
                (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple))
              (@abelian_snake_fourth_psi_cbeta_beta_zero_path C P t Ab A B X D T triple cocone)))))));

symbol abelian_snake_fourth_y_gamma_zero_path
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
      (Hom C
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
        (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_gamma C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
        (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)))
≔ @computational_cokernel_prezero_to_zero_path C
  (@abelian_stability_preadditive C P t Ab) A B
  (@abelian_snake_delta C (@abelian_stability_preadditive C P t Ab) A B X D triple)
  (@abelian_snake_delta_cokernel C P t Ab A B X D triple)
  (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)
  (@comp_fapp0 C _ _ _
    (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone)
    (@abelian_snake_gamma C P t Ab A B X D triple))
  (@abelian_snake_fourth_y_gamma_epsilon_zero_path C P t Ab A B X D T triple cocone);
