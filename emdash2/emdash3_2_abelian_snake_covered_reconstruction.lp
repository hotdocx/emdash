/*
  The actual snake connecting arrow reconstructs its canonical lambda lift
  after the existing epic cover. No new structure or equation is assumed.
*/
require open emdash.emdash3_2_abelian_snake_connecting;

// partial o p1 = pi o L, with L the original lift of beta o p2.
symbol abelian_snake_connecting_after_p1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_connecting C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple)))
≔ (@abelian_snake_q2_monic C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_connecting C P t Ab A B X D triple)
      (@abelian_snake_p1 C P t Ab A B X D triple))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_pi C P t Ab A B X D triple)
      (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_q2 C P t Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple))
          (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple))
          (λ h : τ (Hom C
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple)),
            @comp_fapp0 C _ _ _ h
              (@abelian_snake_p1 C P t Ab A B X D triple))
          _ _ (@abelian_snake_connecting_path C P t Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@abelian_snake_u_path C P t Ab A B X D triple)
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C (@abelian_snake_fiber_object C P t Ab A B X D triple) X)
              (Hom C
                (@abelian_snake_fiber_object C P t Ab A B X D triple)
                (@abelian_snake_pushout_object C P t Ab A B X D triple))
              (λ h : τ (Hom C
                (@abelian_snake_fiber_object C P t Ab A B X D triple) X),
                @comp_fapp0 C _ _ _
                  (@abelian_snake_q1 C P t Ab A B X D triple) h)
              _ _ (@eq_sym _ _ _
                (@abelian_snake_beta_p2_lambda_lift_path C P t Ab A B X D triple)))
            (@eq_trans _ _ _ _
              (@comp_assoc C _ _ _ _
                (@abelian_snake_q1 C P t Ab A B X D triple)
                (@abelian_snake_mu C P t Ab A B X D triple)
                (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple))
              (@eq_trans _ _ _ _
                (@eq_ap
                  (Hom C
                    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
                    (@abelian_snake_pushout_object C P t Ab A B X D triple))
                  (Hom C
                    (@abelian_snake_fiber_object C P t Ab A B X D triple)
                    (@abelian_snake_pushout_object C P t Ab A B X D triple))
                  (λ h : τ (Hom C
                    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
                    (@abelian_snake_pushout_object C P t Ab A B X D triple)),
                    @comp_fapp0 C _ _ _ h
                      (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple))
                  _ _ (@abelian_snake_pushout_compatibility_path C P t Ab A B X D triple))
                (@eq_sym _ _ _
                  (@comp_assoc C _ _ _ _
                    (@abelian_snake_q2 C P t Ab A B X D triple)
                    (@abelian_snake_pi C P t Ab A B X D triple)
                    (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple)))))))));
