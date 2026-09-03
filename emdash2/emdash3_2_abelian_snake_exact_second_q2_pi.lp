/* Pushout reconstruction identifies q2 o pi o xi with u o p1. */

require open emdash.emdash3_2_abelian_snake_exact_second_xi;

symbol abelian_snake_second_q2_pi_xi_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
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
      (@comp_fapp0 C _ _ _
        (@abelian_snake_u C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_p1 C P t Ab A B X D triple)
          (@abelian_snake_second_cover_fiber_lift C P t
            Ab A B X D T triple cone))))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_q2 C P t Ab A B X D triple)
      (@abelian_snake_pi C P t Ab A B X D triple)
      (@abelian_snake_second_cover_xi C P t
        Ab A B X D T triple cone))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_second_cover_object C P t
            Ab A B X D T triple cone)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_second_cover_xi C P t
              Ab A B X D T triple cone))
        _ _
        (@eq_sym _ _ _
          (@computational_pushout_compatibility_path C P t
            (@abelian_stability_additive C P t Ab)
            X
            (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_mu C P t Ab A B X D triple)
            (@abelian_snake_pi C P t Ab A B X D triple)
            (@abelian_snake_pushout C P t Ab A B X D triple))))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_q1 C P t Ab A B X D triple)
            (@abelian_snake_mu C P t Ab A B X D triple)
            (@abelian_snake_second_cover_xi C P t
              Ab A B X D T triple cone)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_second_cover_object C P t
                Ab A B X D T triple cone)
              X)
            (Hom C
              (@abelian_snake_second_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_pushout_object C P t Ab A B X D triple))
            (λ h : τ (Hom C
                (@abelian_snake_second_cover_object C P t
                  Ab A B X D T triple cone)
                X),
              @comp_fapp0 C _ _ _
                (@abelian_snake_q1 C P t Ab A B X D triple) h)
            _ _
            (@abelian_snake_second_cover_xi_path C P t
              Ab A B X D T triple cone))
          (@eq_trans _ _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_q1 C P t Ab A B X D triple)
              (@abelian_snake_beta C
                (@abelian_stability_preadditive C P t Ab) A B X D triple)
              (@comp_fapp0 C _ _ _
                (@abelian_snake_p2 C P t Ab A B X D triple)
                (@abelian_snake_second_cover_fiber_lift C P t
                  Ab A B X D T triple cone)))
            (@eq_trans _ _ _ _
              (@comp_assoc C _ _ _ _
                (@comp_fapp0 C _ _ _
                  (@abelian_snake_q1 C P t Ab A B X D triple)
                  (@abelian_snake_beta C
                    (@abelian_stability_preadditive C P t Ab)
                    A B X D triple))
                (@abelian_snake_p2 C P t Ab A B X D triple)
                (@abelian_snake_second_cover_fiber_lift C P t
                  Ab A B X D T triple cone))
              (@eq_trans _ _ _ _
                (@eq_ap
                  (Hom C
                    (@abelian_snake_fiber_object C P t Ab A B X D triple)
                    (@abelian_snake_pushout_object C P t Ab A B X D triple))
                  (Hom C
                    (@abelian_snake_second_cover_object C P t
                      Ab A B X D T triple cone)
                    (@abelian_snake_pushout_object C P t Ab A B X D triple))
                  (λ h : τ (Hom C
                      (@abelian_snake_fiber_object C P t Ab A B X D triple)
                      (@abelian_snake_pushout_object C P t Ab A B X D triple)),
                    @comp_fapp0 C _ _ _ h
                      (@abelian_snake_second_cover_fiber_lift C P t
                        Ab A B X D T triple cone))
                  _ _
                  (@eq_sym _ _ _
                    (@abelian_snake_u_path C P t Ab A B X D triple)))
                (@eq_sym _ _ _
                  (@comp_assoc C _ _ _ _
                    (@abelian_snake_u C P t Ab A B X D triple)
                    (@abelian_snake_p1 C P t Ab A B X D triple)
                    (@abelian_snake_second_cover_fiber_lift C P t
                      Ab A B X D T triple cone)))))))));
