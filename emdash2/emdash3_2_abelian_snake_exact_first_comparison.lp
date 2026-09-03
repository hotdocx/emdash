/* The lifted row cover reconstructs the first six-term arrow. */

require open emdash.emdash3_2_abelian_snake_exact_first_factor;

symbol abelian_snake_first_cover_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple)
        (@abelian_snake_first_cover_kernel_factor C P t
          Ab A B X D T triple cone))
      (@comp_fapp0 C _ _ _
        (@weak_kernel_annihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_ker_beta_to_ker_gamma C P t
            Ab A B X D triple)
          T cone)
        (@abelian_snake_first_row_cover_epi C P t
          Ab A B X D T triple cone)))
≔ (@computational_kernel_morphism_is_monic C
    (@abelian_stability_preadditive C P t Ab)
    B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple))
    (@abelian_snake_first_row_cover_object C P t
      Ab A B X D T triple cone)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple)
      (@abelian_snake_first_cover_kernel_factor C P t
        Ab A B X D T triple cone))
    (@comp_fapp0 C _ _ _
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
        T cone)
      (@abelian_snake_first_row_cover_epi C P t
        Ab A B X D T triple cone))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_k_beta C P t Ab A B X D triple)
        (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple)
        (@abelian_snake_first_cover_kernel_factor C P t
          Ab A B X D T triple cone))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
            B)
          (Hom C
            (@abelian_snake_first_row_cover_object C P t
              Ab A B X D T triple cone)
            B)
          (λ h : τ (Hom C
              (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
              B),
            @comp_fapp0 C _ _ _ h
              (@abelian_snake_first_cover_kernel_factor C P t
                Ab A B X D T triple cone))
          _ _
          (@abelian_snake_ker_alpha_to_ker_beta_path C P t
            Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_delta C
                (@abelian_stability_preadditive C P t Ab) A B X D triple)
              (@abelian_snake_k_alpha C P t Ab A B X D triple)
              (@abelian_snake_first_cover_kernel_factor C P t
                Ab A B X D T triple cone)))
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C
                (@abelian_snake_first_row_cover_object C P t
                  Ab A B X D T triple cone)
                A)
              (Hom C
                (@abelian_snake_first_row_cover_object C P t
                  Ab A B X D T triple cone)
                B)
              (λ h : τ (Hom C
                  (@abelian_snake_first_row_cover_object C P t
                    Ab A B X D T triple cone)
                  A),
                @comp_fapp0 C _ _ _
                  (@abelian_snake_delta C
                    (@abelian_stability_preadditive C P t Ab)
                    A B X D triple) h)
              _ _
              (@abelian_snake_first_cover_kernel_factor_path C P t
                Ab A B X D T triple cone))
            (@eq_trans _ _ _ _
              (@abelian_snake_first_row_cover_path C P t
                Ab A B X D T triple cone)
              (@eq_sym _ _ _
                (@comp_assoc C _ _ _ _
                  (@abelian_snake_k_beta C P t Ab A B X D triple)
                  (@weak_kernel_annihilator_arrow C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_ker_beta_object C P t
                      Ab A B X D triple)
                    (@abelian_snake_ker_gamma_object C P t
                      Ab A B X D triple)
                    (@abelian_snake_ker_beta_to_ker_gamma C P t
                      Ab A B X D triple)
                    T cone)
                  (@abelian_snake_first_row_cover_epi C P t
                    Ab A B X D T triple cone))))))));
