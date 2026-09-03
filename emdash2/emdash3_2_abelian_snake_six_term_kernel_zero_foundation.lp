/* Kernel-side calculated zero before monic cancellation. */

require open emdash.emdash3_2_abelian_snake_six_term_cokernels;

symbol abelian_snake_iota_after_kernel_composite_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@computational_kernel_morphism C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
          (@abelian_snake_gamma C P t Ab A B X D triple)
          (@abelian_snake_gamma_kernel C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _
          (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
          (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@computational_kernel_morphism C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_gamma_kernel C P t Ab A B X D triple))
      (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
      (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple))
        _ _
        (@abelian_snake_ker_beta_to_ker_gamma_path C P t
          Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_epsilon C P t Ab A B X D triple)
            (@abelian_snake_k_beta C P t Ab A B X D triple)
            (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) B)
            (Hom C
              (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
            (λ h : τ (Hom C
                (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) B),
              @comp_fapp0 C _ _ _
                (@abelian_snake_epsilon C P t Ab A B X D triple) h)
            _ _
            (@abelian_snake_ker_alpha_to_ker_beta_path C P t
              Ab A B X D triple))
          (@eq_trans _ _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_epsilon C P t Ab A B X D triple)
              (@abelian_snake_delta C
                (@abelian_stability_preadditive C P t Ab) A B X D triple)
              (@abelian_snake_k_alpha C P t Ab A B X D triple))
            (@eq_trans _ _ _ _
              (@eq_ap
                (Hom C A
                  (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
                (Hom C
                  (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
                  (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
                (λ h : τ (Hom C A
                    (@abelian_snake_coker_delta_object C P t
                      Ab A B X D triple)),
                  @comp_fapp0 C _ _ _ h
                    (@abelian_snake_k_alpha C P t Ab A B X D triple))
                _ _
                (@computational_cokernel_annihilation C
                  (@abelian_stability_preadditive C P t Ab) A B
                  (@abelian_snake_delta C
                    (@abelian_stability_preadditive C P t Ab) A B X D triple)
                  (@abelian_snake_delta_cokernel C P t Ab A B X D triple)))
              (@preadditive_comp_zero_left_path C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
                A
                (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
                (@abelian_snake_k_alpha C P t Ab A B X D triple)))))));
