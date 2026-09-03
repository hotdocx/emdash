/* Cokernel-side calculated zero before epic cancellation. */

require open emdash.emdash3_2_abelian_snake_six_term_cokernels;

symbol abelian_snake_cokernel_composite_after_pi_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple))
        (@computational_cokernel_morphism C
          (@abelian_stability_preadditive C P t Ab) A
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_alpha C P t Ab A B X D triple)
          (@abelian_snake_alpha_cokernel C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
        (@computational_cokernel_morphism C
          (@abelian_stability_preadditive C P t Ab) A
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_alpha C P t Ab A B X D triple)
          (@abelian_snake_alpha_cokernel C P t Ab A B X D triple))))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _
            (@abelian_snake_coker_beta_to_coker_gamma C P t
              Ab A B X D triple) h)
        _ _
        (@abelian_snake_coker_alpha_to_coker_beta_path C P t
          Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_coker_beta_to_coker_gamma C P t
              Ab A B X D triple)
            (@abelian_snake_c_beta C P t Ab A B X D triple)
            (@abelian_snake_mu C P t Ab A B X D triple)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C X
              (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
            (Hom C
              (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
              (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
            (λ h : τ (Hom C X
                (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_mu C P t Ab A B X D triple))
            _ _
            (@abelian_snake_coker_beta_to_coker_gamma_path C P t
              Ab A B X D triple))
          (@eq_trans _ _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_c_gamma C P t Ab A B X D triple)
              (@abelian_snake_lambda C
                (@abelian_stability_preadditive C P t Ab) A B X D triple)
              (@abelian_snake_mu C P t Ab A B X D triple))
            (@eq_trans _ _ _ _
              (@eq_ap
                (Hom C
                  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) D)
                (Hom C
                  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
                  (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
                (λ h : τ (Hom C
                    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) D),
                  @comp_fapp0 C _ _ _
                    (@abelian_snake_c_gamma C P t Ab A B X D triple) h)
                _ _
                (@computational_kernel_annihilation C
                  (@abelian_stability_preadditive C P t Ab) X D
                  (@abelian_snake_lambda C
                    (@abelian_stability_preadditive C P t Ab) A B X D triple)
                  (@abelian_snake_lambda_kernel C P t Ab A B X D triple)))
              (@preadditive_comp_zero_right_path C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
                D
                (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
                (@abelian_snake_c_gamma C P t Ab A B X D triple)))))));
