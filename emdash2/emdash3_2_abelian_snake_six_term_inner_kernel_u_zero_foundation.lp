/* Middle map vanishes on the selected Ker(beta) fiber factor. */

require open emdash.emdash3_2_abelian_snake_normal_epi;
require open emdash.emdash3_2_abelian_snake_six_term_inner_kernel_factor;

symbol abelian_snake_u_after_ker_beta_map_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_u C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_ap
      (Hom C
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (Hom C
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (λ h : τ (Hom C
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
        @comp_fapp0 C _ _ _
          (@abelian_snake_u C P t Ab A B X D triple) h)
      _ _
      (@eq_sym _ _ _
        (@abelian_snake_k_beta_fiber_lift_p1_path C P t
          Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_u C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple)
        (@abelian_snake_k_beta_fiber_lift C P t Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple))
          (Hom C
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple))
          (λ h : τ (Hom C
              (@abelian_snake_fiber_object C P t Ab A B X D triple)
              (@abelian_snake_pushout_object C P t Ab A B X D triple)),
            @comp_fapp0 C _ _ _ h
              (@abelian_snake_k_beta_fiber_lift C P t Ab A B X D triple))
          _ _
          (@abelian_snake_u_path C P t Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _
            (@comp_assoc C _ _ _ _
              (@comp_fapp0 C _ _ _
                (@abelian_snake_q1 C P t Ab A B X D triple)
                (@abelian_snake_beta C
                  (@abelian_stability_preadditive C P t Ab) A B X D triple))
              (@abelian_snake_p2 C P t Ab A B X D triple)
              (@abelian_snake_k_beta_fiber_lift C P t Ab A B X D triple)))
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C
                (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B)
              (Hom C
                (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                (@abelian_snake_pushout_object C P t Ab A B X D triple))
              (λ h : τ (Hom C
                  (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B),
                @comp_fapp0 C _ _ _
                  (@comp_fapp0 C _ _ _
                    (@abelian_snake_q1 C P t Ab A B X D triple)
                    (@abelian_snake_beta C
                      (@abelian_stability_preadditive C P t Ab)
                      A B X D triple))
                  h)
              _ _
              (@abelian_snake_k_beta_fiber_lift_p2_path C P t
                Ab A B X D triple))
            (@eq_trans _ _ _ _
              (@eq_sym _ _ _
                (@comp_assoc C _ _ _ _
                  (@abelian_snake_q1 C P t Ab A B X D triple)
                  (@abelian_snake_beta C
                    (@abelian_stability_preadditive C P t Ab) A B X D triple)
                  (@abelian_snake_k_beta C P t Ab A B X D triple)))
              (@eq_trans _ _ _ _
                (@eq_ap
                  (Hom C
                    (@abelian_snake_ker_beta_object C P t Ab A B X D triple) X)
                  (Hom C
                    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                    (@abelian_snake_pushout_object C P t Ab A B X D triple))
                  (λ h : τ (Hom C
                      (@abelian_snake_ker_beta_object C P t Ab A B X D triple) X),
                    @comp_fapp0 C _ _ _
                      (@abelian_snake_q1 C P t Ab A B X D triple) h)
                  _ _
                  (@abelian_snake_beta_k_beta_zero_path C P t
                    Ab A B X D triple))
                (@preadditive_comp_zero_right_path C
                  (@abelian_stability_preadditive C P t Ab)
                  (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                  X
                  (@abelian_snake_pushout_object C P t Ab A B X D triple)
                  (@abelian_snake_q1 C P t Ab A B X D triple))))))));
