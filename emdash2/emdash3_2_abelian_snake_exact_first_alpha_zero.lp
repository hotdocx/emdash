/* The first row-cover preimage lies in Ker(alpha). */

require open emdash.emdash3_2_abelian_snake_exact_first_row_cover_projections;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_mu_alpha_after_first_row_cover_zero_path
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
      X)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_alpha C P t Ab A B X D triple)
          (@abelian_snake_first_row_cover_factor C P t
            Ab A B X D T triple cone)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_first_row_cover_object C P t
          Ab A B X D T triple cone)
        X))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_mu C P t Ab A B X D triple)
      (@abelian_snake_alpha C P t Ab A B X D triple)
      (@abelian_snake_first_row_cover_factor C P t
        Ab A B X D T triple cone))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C A X)
        (Hom C
          (@abelian_snake_first_row_cover_object C P t
            Ab A B X D T triple cone)
          X)
        (λ h : τ (Hom C A X),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_first_row_cover_factor C P t
              Ab A B X D T triple cone))
        _ _
        (@abelian_snake_alpha_path C P t Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_beta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)
            (@abelian_snake_delta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)
            (@abelian_snake_first_row_cover_factor C P t
              Ab A B X D T triple cone)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_first_row_cover_object C P t
                Ab A B X D T triple cone)
              B)
            (Hom C
              (@abelian_snake_first_row_cover_object C P t
                Ab A B X D T triple cone)
              X)
            (λ h : τ (Hom C
                (@abelian_snake_first_row_cover_object C P t
                  Ab A B X D T triple cone)
                B),
              @comp_fapp0 C _ _ _
                (@abelian_snake_beta C
                  (@abelian_stability_preadditive C P t Ab)
                  A B X D triple) h)
            _ _
            (@abelian_snake_first_row_cover_path C P t
              Ab A B X D T triple cone))
          (@eq_trans _ _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_beta C
                (@abelian_stability_preadditive C P t Ab) A B X D triple)
              (@comp_fapp0 C _ _ _
                (@abelian_snake_k_beta C P t Ab A B X D triple)
                (@weak_kernel_annihilator_arrow C
                  (@abelian_stability_preadditive C P t Ab)
                  (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                  (@abelian_snake_ker_beta_to_ker_gamma C P t
                    Ab A B X D triple)
                  T cone))
              (@abelian_snake_first_row_cover_epi C P t
                Ab A B X D T triple cone))
            (@eq_trans _ _ _ _
              (@eq_ap
                (Hom C T X)
                (Hom C
                  (@abelian_snake_first_row_cover_object C P t
                    Ab A B X D T triple cone)
                  X)
                (λ h : τ (Hom C T X),
                  @comp_fapp0 C _ _ _ h
                    (@abelian_snake_first_row_cover_epi C P t
                      Ab A B X D T triple cone))
                _ _
                (@comp_assoc C _ _ _ _
                  (@abelian_snake_beta C
                    (@abelian_stability_preadditive C P t Ab)
                    A B X D triple)
                  (@abelian_snake_k_beta C P t Ab A B X D triple)
                  (@weak_kernel_annihilator_arrow C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                    (@abelian_snake_ker_beta_to_ker_gamma C P t
                      Ab A B X D triple)
                    T cone)))
              (@eq_trans _ _ _ _
                (@eq_ap
                  (Hom C
                    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                    X)
                  (Hom C
                    (@abelian_snake_first_row_cover_object C P t
                      Ab A B X D T triple cone)
                    X)
                  (λ h : τ (Hom C
                      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                      X),
                    @comp_fapp0 C _ _ _
                      (@comp_fapp0 C _ _ _ h
                        (@weak_kernel_annihilator_arrow C
                          (@abelian_stability_preadditive C P t Ab)
                          (@abelian_snake_ker_beta_object C P t
                            Ab A B X D triple)
                          (@abelian_snake_ker_gamma_object C P t
                            Ab A B X D triple)
                          (@abelian_snake_ker_beta_to_ker_gamma C P t
                            Ab A B X D triple)
                          T cone))
                      (@abelian_snake_first_row_cover_epi C P t
                        Ab A B X D T triple cone))
                  _ _
                  (@abelian_snake_beta_k_beta_zero_path C P t
                    Ab A B X D triple))
                (@eq_trans _ _ _ _
                  (@eq_ap
                    (Hom C T X)
                    (Hom C
                      (@abelian_snake_first_row_cover_object C P t
                        Ab A B X D T triple cone)
                      X)
                    (λ h : τ (Hom C T X),
                      @comp_fapp0 C _ _ _ h
                        (@abelian_snake_first_row_cover_epi C P t
                          Ab A B X D T triple cone))
                    _ _
                    (@preadditive_comp_zero_left_path C
                      (@abelian_stability_preadditive C P t Ab)
                      T
                      (@abelian_snake_ker_beta_object C P t
                        Ab A B X D triple)
                      X
                      (@weak_kernel_annihilator_arrow C
                        (@abelian_stability_preadditive C P t Ab)
                        (@abelian_snake_ker_beta_object C P t
                          Ab A B X D triple)
                        (@abelian_snake_ker_gamma_object C P t
                          Ab A B X D triple)
                        (@abelian_snake_ker_beta_to_ker_gamma C P t
                          Ab A B X D triple)
                        T cone)))
                  (@preadditive_comp_zero_left_path C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_first_row_cover_object C P t
                      Ab A B X D T triple cone)
                    T X
                    (@abelian_snake_first_row_cover_epi C P t
                      Ab A B X D T triple cone)))))))));

symbol abelian_snake_first_row_cover_alpha_zero_path
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
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_alpha C P t Ab A B X D triple)
        (@abelian_snake_first_row_cover_factor C P t
          Ab A B X D T triple cone))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_first_row_cover_object C P t
          Ab A B X D T triple cone)
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)))
≔ @monic_postcomposition_zero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_first_row_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    X
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_mu_monic C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_alpha C P t Ab A B X D triple)
      (@abelian_snake_first_row_cover_factor C P t
        Ab A B X D T triple cone))
    (@abelian_snake_mu_alpha_after_first_row_cover_zero_path C P t
      Ab A B X D T triple cone);
