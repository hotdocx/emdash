/* The first pullback lift becomes a cone for Coker(alpha). */

require open emdash.emdash3_2_abelian_snake_exact_second_q2_pi;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_second_q2_pi_xi_zero_path
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
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q2 C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_pi C P t Ab A B X D triple)
          (@abelian_snake_second_cover_xi C P t
            Ab A B X D T triple cone)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_second_cover_object C P t
          Ab A B X D T triple cone)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@abelian_snake_second_q2_pi_xi_path C P t
      Ab A B X D T triple cone)
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_second_cover_object C P t
            Ab A B X D T triple cone)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_second_cover_object C P t
            Ab A B X D T triple cone)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_second_cover_object C P t
              Ab A B X D T triple cone)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _
            (@abelian_snake_u C P t Ab A B X D triple) h)
        _ _
        (@eq_sym _ _ _
          (@abelian_snake_second_cover_path C P t
            Ab A B X D T triple cone)))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_u C P t Ab A B X D triple)
          (@weak_kernel_annihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_connecting C P t Ab A B X D triple)
            T cone)
          (@abelian_snake_second_cover_epi C P t
            Ab A B X D T triple cone))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C T
              (@abelian_snake_pushout_object C P t Ab A B X D triple))
            (Hom C
              (@abelian_snake_second_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_pushout_object C P t Ab A B X D triple))
            (λ h : τ (Hom C T
                (@abelian_snake_pushout_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_second_cover_epi C P t
                  Ab A B X D T triple cone))
            _ _
            (@eq_ap
              (Hom C
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                (@abelian_snake_pushout_object C P t Ab A B X D triple))
              (Hom C T
                (@abelian_snake_pushout_object C P t Ab A B X D triple))
              (λ h : τ (Hom C
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                  (@abelian_snake_pushout_object C P t Ab A B X D triple)),
                @comp_fapp0 C _ _ _ h
                  (@weak_kernel_annihilator_arrow C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                    (@abelian_snake_connecting C P t Ab A B X D triple)
                    T cone))
              _ _
              (@eq_sym _ _ _
                (@abelian_snake_connecting_path C P t Ab A B X D triple))))
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C T
                (@abelian_snake_pushout_object C P t Ab A B X D triple))
              (Hom C
                (@abelian_snake_second_cover_object C P t
                  Ab A B X D T triple cone)
                (@abelian_snake_pushout_object C P t Ab A B X D triple))
              (λ h : τ (Hom C T
                  (@abelian_snake_pushout_object C P t Ab A B X D triple)),
                @comp_fapp0 C _ _ _ h
                  (@abelian_snake_second_cover_epi C P t
                    Ab A B X D T triple cone))
              _ _
              (@eq_sym _ _ _
                (@comp_assoc C _ _ _ _
                  (@abelian_snake_q2 C P t Ab A B X D triple)
                  (@abelian_snake_connecting C P t Ab A B X D triple)
                  (@weak_kernel_annihilator_arrow C
                    (@abelian_stability_preadditive C P t Ab)
                    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                    (@abelian_snake_connecting C P t Ab A B X D triple)
                    T cone))))
            (@eq_trans _ _ _ _
              (@eq_ap
                (Hom C T
                  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
                (Hom C
                  (@abelian_snake_second_cover_object C P t
                    Ab A B X D T triple cone)
                  (@abelian_snake_pushout_object C P t Ab A B X D triple))
                (λ h : τ (Hom C T
                    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)),
                  @comp_fapp0 C _ _ _
                    (@comp_fapp0 C _ _ _
                      (@abelian_snake_q2 C P t Ab A B X D triple) h)
                    (@abelian_snake_second_cover_epi C P t
                      Ab A B X D T triple cone))
                _ _
                (@weak_kernel_annihilator_path C
                  (@abelian_stability_preadditive C P t Ab)
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                  (@abelian_snake_connecting C P t Ab A B X D triple)
                  T cone))
              (@preadditive_precompose_zero_path C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_second_cover_object C P t
                  Ab A B X D T triple cone)
                T
                (@abelian_snake_pushout_object C P t Ab A B X D triple)
                (@comp_fapp0 C _ _ _
                  (@abelian_snake_q2 C P t Ab A B X D triple)
                  (@preadditive_hom_zero C
                    (@abelian_stability_preadditive C P t Ab) T
                    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)))
                (@abelian_snake_second_cover_epi C P t
                  Ab A B X D T triple cone)
                (@preadditive_comp_zero_right_path C
                  (@abelian_stability_preadditive C P t Ab)
                  T
                  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                  (@abelian_snake_pushout_object C P t Ab A B X D triple)
                  (@abelian_snake_q2 C P t Ab A B X D triple))))))));

symbol abelian_snake_second_pi_xi_zero_path
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
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_second_cover_xi C P t
          Ab A B X D T triple cone))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_second_cover_object C P t
          Ab A B X D T triple cone)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)))
≔ @monic_postcomposition_zero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_second_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@abelian_snake_q2_monic C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_pi C P t Ab A B X D triple)
      (@abelian_snake_second_cover_xi C P t
        Ab A B X D T triple cone))
    (@abelian_snake_second_q2_pi_xi_zero_path C P t
      Ab A B X D T triple cone);
