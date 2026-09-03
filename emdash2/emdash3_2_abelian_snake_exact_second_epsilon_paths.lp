/* Epsilon reads the corrected beta-kernel lift as the covered test arrow. */

require open emdash.emdash3_2_abelian_snake_exact_second_kernel_factor;
require open emdash.emdash3_2_preadditive_difference_paths;

symbol abelian_snake_second_epsilon_positive_path
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
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@comp_fapp0 C _ _ _
            (@abelian_snake_p2 C P t Ab A B X D triple)
            (@abelian_snake_second_cover_fiber_lift C P t
              Ab A B X D T triple cone))
          (@abelian_snake_second_alpha_cover_epi C P t
            Ab A B X D T triple cone)))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@comp_fapp0 C _ _ _
            (@weak_kernel_annihilator_arrow C
              (@abelian_stability_preadditive C P t Ab)
              (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
              (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_connecting C P t Ab A B X D triple)
              T cone)
            (@abelian_snake_second_cover_epi C P t
              Ab A B X D T triple cone))
          (@abelian_snake_second_alpha_cover_epi C P t
            Ab A B X D T triple cone))))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_epsilon C P t Ab A B X D triple)
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
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_second_alpha_cover_object C P t
            Ab A B X D T triple cone)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_second_cover_object C P t
              Ab A B X D T triple cone)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_second_alpha_cover_epi C P t
              Ab A B X D T triple cone))
        _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_epsilon C P t Ab A B X D triple)
          (@abelian_snake_p2 C P t Ab A B X D triple)
          (@abelian_snake_second_cover_fiber_lift C P t
            Ab A B X D T triple cone)))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
          (Hom C
            (@abelian_snake_second_alpha_cover_object C P t
              Ab A B X D T triple cone)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
          (λ h : τ (Hom C
              (@abelian_snake_fiber_object C P t Ab A B X D triple)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
            @comp_fapp0 C _ _ _
              (@comp_fapp0 C _ _ _ h
                (@abelian_snake_second_cover_fiber_lift C P t
                  Ab A B X D T triple cone))
              (@abelian_snake_second_alpha_cover_epi C P t
                Ab A B X D T triple cone))
          _ _
          (@eq_sym _ _ _
            (@abelian_snake_fiber_compatibility_path C P t
              Ab A B X D triple)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_second_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
            (Hom C
              (@abelian_snake_second_alpha_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
            (λ h : τ (Hom C
                (@abelian_snake_second_cover_object C P t
                  Ab A B X D T triple cone)
                (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_second_alpha_cover_epi C P t
                  Ab A B X D T triple cone))
            _ _
            (@eq_sym _ _ _
              (@comp_assoc C _ _ _ _
                (@abelian_snake_iota C P t Ab A B X D triple)
                (@abelian_snake_p1 C P t Ab A B X D triple)
                (@abelian_snake_second_cover_fiber_lift C P t
                  Ab A B X D T triple cone))))
          (@eq_trans _ _ _ _
            (@eq_sym _ _ _
              (@comp_assoc C _ _ _ _
                (@abelian_snake_iota C P t Ab A B X D triple)
                (@comp_fapp0 C _ _ _
                  (@abelian_snake_p1 C P t Ab A B X D triple)
                  (@abelian_snake_second_cover_fiber_lift C P t
                    Ab A B X D T triple cone))
                (@abelian_snake_second_alpha_cover_epi C P t
                  Ab A B X D T triple cone)))
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
              (@eq_ap
                (Hom C
                  (@abelian_snake_second_cover_object C P t
                    Ab A B X D T triple cone)
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
                (Hom C
                  (@abelian_snake_second_alpha_cover_object C P t
                    Ab A B X D T triple cone)
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
                (λ h : τ (Hom C
                    (@abelian_snake_second_cover_object C P t
                      Ab A B X D T triple cone)
                    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
                  @comp_fapp0 C _ _ _ h
                    (@abelian_snake_second_alpha_cover_epi C P t
                      Ab A B X D T triple cone))
                _ _
                (@eq_sym _ _ _
                  (@abelian_snake_second_cover_path C P t
                    Ab A B X D T triple cone))))))));

symbol abelian_snake_second_epsilon_negative_zero_path
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
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_second_alpha_cover_factor C P t
            Ab A B X D T triple cone)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_second_alpha_cover_object C P t
          Ab A B X D T triple cone)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_epsilon C P t Ab A B X D triple)
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_second_alpha_cover_factor C P t
        Ab A B X D T triple cone))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C A
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_second_alpha_cover_object C P t
            Ab A B X D T triple cone)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (λ h : τ (Hom C A
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_second_alpha_cover_factor C P t
              Ab A B X D T triple cone))
        _ _
        (@computational_cokernel_annihilation C
          (@abelian_stability_preadditive C P t Ab)
          A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_delta_cokernel C P t Ab A B X D triple)))
      (@preadditive_comp_zero_left_path C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_second_alpha_cover_object C P t
          Ab A B X D T triple cone)
        A
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
        (@abelian_snake_second_alpha_cover_factor C P t
          Ab A B X D T triple cone)));
