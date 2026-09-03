/* The two B-valued lifts agree after beta on the double cover. */

require open emdash.emdash3_2_abelian_snake_exact_second_alpha_cover_factor;

symbol abelian_snake_second_beta_lifts_path
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
      X)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@comp_fapp0 C _ _ _
          (@comp_fapp0 C _ _ _
            (@abelian_snake_p2 C P t Ab A B X D triple)
            (@abelian_snake_second_cover_fiber_lift C P t
              Ab A B X D T triple cone))
          (@abelian_snake_second_alpha_cover_epi C P t
            Ab A B X D T triple cone)))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_second_alpha_cover_factor C P t
            Ab A B X D T triple cone))))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_p2 C P t Ab A B X D triple)
        (@abelian_snake_second_cover_fiber_lift C P t
          Ab A B X D T triple cone))
      (@abelian_snake_second_alpha_cover_epi C P t
        Ab A B X D T triple cone))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_second_cover_object C P t
            Ab A B X D T triple cone)
          X)
        (Hom C
          (@abelian_snake_second_alpha_cover_object C P t
            Ab A B X D T triple cone)
          X)
        (λ h : τ (Hom C
            (@abelian_snake_second_cover_object C P t
              Ab A B X D T triple cone)
            X),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_second_alpha_cover_epi C P t
              Ab A B X D T triple cone))
        _ _
        (@eq_sym _ _ _
          (@abelian_snake_second_cover_xi_path C P t
            Ab A B X D T triple cone)))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_mu C P t Ab A B X D triple)
            (@abelian_snake_second_cover_xi C P t
              Ab A B X D T triple cone)
            (@abelian_snake_second_alpha_cover_epi C P t
              Ab A B X D T triple cone)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_second_alpha_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_ker_lambda_object C P t Ab A B X D triple))
            (Hom C
              (@abelian_snake_second_alpha_cover_object C P t
                Ab A B X D T triple cone)
              X)
            (λ h : τ (Hom C
                (@abelian_snake_second_alpha_cover_object C P t
                  Ab A B X D T triple cone)
                (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _
                (@abelian_snake_mu C P t Ab A B X D triple) h)
            _ _
            (@eq_sym _ _ _
              (@abelian_snake_second_alpha_cover_path C P t
                Ab A B X D T triple cone)))
          (@eq_trans _ _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_mu C P t Ab A B X D triple)
              (@abelian_snake_alpha C P t Ab A B X D triple)
              (@abelian_snake_second_alpha_cover_factor C P t
                Ab A B X D T triple cone))
            (@eq_trans _ _ _ _
              (@eq_ap
                (Hom C A X)
                (Hom C
                  (@abelian_snake_second_alpha_cover_object C P t
                    Ab A B X D T triple cone)
                  X)
                (λ h : τ (Hom C A X),
                  @comp_fapp0 C _ _ _ h
                    (@abelian_snake_second_alpha_cover_factor C P t
                      Ab A B X D T triple cone))
                _ _
                (@abelian_snake_alpha_path C P t Ab A B X D triple))
              (@eq_sym _ _ _
                (@comp_assoc C _ _ _ _
                  (@abelian_snake_beta C
                    (@abelian_stability_preadditive C P t Ab)
                    A B X D triple)
                  (@abelian_snake_delta C
                    (@abelian_stability_preadditive C P t Ab)
                    A B X D triple)
                  (@abelian_snake_second_alpha_cover_factor C P t
                    Ab A B X D T triple cone))))))));
