/* After p1, zeta o iota agrees with the extended u. */

require open emdash.emdash3_2_abelian_snake_exact_third_zeta_epsilon;

symbol abelian_snake_third_zeta_iota_after_p1_to_su_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_third_zeta C P t
            Ab A B X D T triple cocone)
          (@abelian_snake_iota C P t Ab A B X D triple))
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_third_extension_pushout_factor C P t
            Ab A B X D T triple cocone)
          (@abelian_snake_u C P t Ab A B X D triple))
        (@abelian_snake_p1 C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_third_zeta C P t
          Ab A B X D T triple cocone)
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_third_extension_object C P t
            Ab A B X D T triple cocone))
        (λ h : τ (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _
            (@abelian_snake_third_zeta C P t
              Ab A B X D T triple cocone) h)
        _ _
        (@abelian_snake_fiber_compatibility_path C P t
          Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_third_zeta C P t
            Ab A B X D T triple cocone)
          (@abelian_snake_epsilon C P t Ab A B X D triple)
          (@abelian_snake_p2 C P t Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C B
              (@abelian_snake_third_extension_object C P t
                Ab A B X D T triple cocone))
            (Hom C
              (@abelian_snake_fiber_object C P t Ab A B X D triple)
              (@abelian_snake_third_extension_object C P t
                Ab A B X D T triple cocone))
            (λ h : τ (Hom C B
                (@abelian_snake_third_extension_object C P t
                  Ab A B X D T triple cocone)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_p2 C P t Ab A B X D triple))
            _ _
            (@abelian_snake_third_zeta_epsilon_path C P t
              Ab A B X D T triple cocone))
          (@eq_trans _ _ _ _
            (@eq_sym _ _ _
              (@comp_assoc C _ _ _ _
                (@abelian_snake_third_extension_pushout_factor C P t
                  Ab A B X D T triple cocone)
                (@abelian_snake_q1_beta C P t Ab A B X D triple)
                (@abelian_snake_p2 C P t Ab A B X D triple)))
            (@eq_trans _ _ _ _
              (@eq_ap
                (Hom C
                  (@abelian_snake_fiber_object C P t Ab A B X D triple)
                  (@abelian_snake_pushout_object C P t Ab A B X D triple))
                (Hom C
                  (@abelian_snake_fiber_object C P t Ab A B X D triple)
                  (@abelian_snake_third_extension_object C P t
                    Ab A B X D T triple cocone))
                (λ h : τ (Hom C
                    (@abelian_snake_fiber_object C P t Ab A B X D triple)
                    (@abelian_snake_pushout_object C P t Ab A B X D triple)),
                  @comp_fapp0 C _ _ _
                    (@abelian_snake_third_extension_pushout_factor C P t
                      Ab A B X D T triple cocone) h)
                _ _
                (@eq_sym _ _ _
                  (@abelian_snake_u_path C P t Ab A B X D triple)))
              (@comp_assoc C _ _ _ _
                (@abelian_snake_third_extension_pushout_factor C P t
                  Ab A B X D T triple cocone)
                (@abelian_snake_u C P t Ab A B X D triple)
                (@abelian_snake_p1 C P t Ab A B X D triple)))))));
