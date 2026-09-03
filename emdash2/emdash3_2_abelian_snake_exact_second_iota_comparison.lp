/* Calculation after the selected monic Ker(gamma) embedding. */

require open emdash.emdash3_2_abelian_snake_exact_second_epsilon_factor;

symbol abelian_snake_second_iota_cover_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_second_alpha_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
          (@abelian_snake_second_kernel_factor C P t
            Ab A B X D T triple cone)))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@weak_kernel_annihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_connecting C P t Ab A B X D triple)
            T cone)
          (@comp_fapp0 C _ _ _
            (@abelian_snake_second_cover_epi C P t
              Ab A B X D T triple cone)
            (@abelian_snake_second_alpha_cover_epi C P t
              Ab A B X D T triple cone)))))
≔ (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
        (@abelian_snake_second_kernel_factor C P t
          Ab A B X D T triple cone))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
          (Hom C
            (@abelian_snake_second_alpha_cover_object C P t
              Ab A B X D T triple cone)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
          (λ h : τ (Hom C
              (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
            @comp_fapp0 C _ _ _ h
              (@abelian_snake_second_kernel_factor C P t
                Ab A B X D T triple cone))
          _ _
          (@abelian_snake_ker_beta_to_ker_gamma_path C P t
            Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_epsilon C P t Ab A B X D triple)
              (@abelian_snake_k_beta C P t Ab A B X D triple)
              (@abelian_snake_second_kernel_factor C P t
                Ab A B X D T triple cone)))
          (@eq_trans _ _ _ _
            (@abelian_snake_second_epsilon_kernel_factor_path C P t
              Ab A B X D T triple cone)
            (@eq_ap
              (Hom C
                (@abelian_snake_second_alpha_cover_object C P t
                  Ab A B X D T triple cone)
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
              (Hom C
                (@abelian_snake_second_alpha_cover_object C P t
                  Ab A B X D T triple cone)
                (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
              (λ h : τ (Hom C
                  (@abelian_snake_second_alpha_cover_object C P t
                    Ab A B X D T triple cone)
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
                @comp_fapp0 C _ _ _
                  (@abelian_snake_iota C P t Ab A B X D triple) h)
              _ _
              (@eq_sym _ _ _
                (@comp_assoc C _ _ _ _
                  (@weak_kernel_annihilator_arrow C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                    (@abelian_snake_connecting C P t Ab A B X D triple)
                    T cone)
                  (@abelian_snake_second_cover_epi C P t
                    Ab A B X D T triple cone)
                  (@abelian_snake_second_alpha_cover_epi C P t
                    Ab A B X D T triple cone))))))));
