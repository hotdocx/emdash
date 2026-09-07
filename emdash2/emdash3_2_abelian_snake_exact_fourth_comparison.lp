/* Reconstruct after c_beta and cancel its epicity. */

require open emdash.emdash3_2_abelian_snake_exact_fourth_cokernel_factor;

symbol abelian_snake_fourth_cbeta_comparison_path
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
      (Hom C X (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
          (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple))
        (@abelian_snake_c_beta C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
          (@cokernel_coannihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone))
        (@abelian_snake_c_beta C P t Ab A B X D triple)))
≔
  (@eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
        (@abelian_snake_c_beta C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C X (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
        (Hom C X (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
        (λ h : τ
          (Hom C X (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
          (@comp_fapp0 C _ _ _
            (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone) h))
        _ _
        (@abelian_snake_coker_beta_to_coker_gamma_path C P t Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
          (@abelian_snake_c_gamma C P t Ab A B X D triple)
          (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C D (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
            (Hom C X (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
            (λ h : τ
              (Hom C D (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)),
              (@comp_fapp0 C _ _ _ h
                (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple)))
            _ _
            (@abelian_snake_fourth_cokernel_factor_path C P t Ab A B X D T triple cocone))
          (@eq_trans _ _ _ _
            (@eq_sym _ _ _ (@abelian_snake_fourth_extension_path C P t Ab A B X D T triple cocone))
            (@comp_assoc C _ _ _ _
              (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
              (@cokernel_coannihilator_arrow C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
                (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
              (@abelian_snake_c_beta C P t Ab A B X D triple)))))));

symbol abelian_snake_fourth_extension_comparison_path
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
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
        (@cokernel_coannihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)))
≔ @eq_sym
  (Hom C
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
  (@comp_fapp0 C _ _ _
    (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
    (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple))
  (@comp_fapp0 C _ _ _
    (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone))
  (
    (@computational_cokernel_morphism_is_epic C
      (@abelian_stability_preadditive C P t Ab) B X
      (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_beta_cokernel C P t Ab A B X D triple))
    (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
      (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
      (@cokernel_coannihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone))
    (@abelian_snake_fourth_cbeta_comparison_path C P t Ab A B X D T triple cocone));
