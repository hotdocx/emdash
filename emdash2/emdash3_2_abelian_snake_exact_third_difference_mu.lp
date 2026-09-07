/* The right coextension vanishes after mu, so the difference reconstructs. */

require open emdash.emdash3_2_abelian_snake_exact_third_mu_reconstruction;
require open emdash.emdash3_2_preadditive_difference_paths;

symbol abelian_snake_third_right_mu_zero_path
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
    (@abelian_snake_connecting C P t Ab A B X D triple) T))
  : τ (@= (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _ (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_factor C P t
        Ab A B X D T triple cocone) (@abelian_snake_lambda C (@abelian_stability_preadditive C P t
        Ab) A B X D triple)) (@abelian_snake_mu C P t Ab A B X D triple))
      (@preadditive_hom_zero C (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ (@abelian_snake_third_gamma_extension_factor C P t Ab A B
      X D T triple cocone) (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X
      D triple) (@abelian_snake_mu C P t Ab A B X D triple)))
    (@preadditive_postcompose_zero_path C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) D
        (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
        (@abelian_snake_third_gamma_extension_factor C P t Ab A B X D T triple cocone) (@comp_fapp0
        C _ _ _ (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple))
      (@computational_kernel_annihilation C (@abelian_stability_preadditive C P t Ab) X D
        (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_lambda_kernel C P t Ab A B X D triple)));

symbol abelian_snake_third_difference_mu_path
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
    (@abelian_snake_connecting C P t Ab A B X D triple) T))
  : τ (@= (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)) (@comp_fapp0 C _
    _ _ (@preadditive_hom_add C (@abelian_stability_preadditive C P t Ab) X
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone) (@comp_fapp0 C _
    _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
    (@comp_fapp0 C _ _ _ (@abelian_snake_third_extension_pushout_factor C P t Ab A B X D T triple
    cocone) (@abelian_snake_q1 C P t Ab A B X D triple)))
        (@preadditive_hom_neg C (@abelian_stability_preadditive C P t Ab) X
          (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
          (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_factor C P t Ab A B X D T
          triple cocone) (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D
          triple)))) (@abelian_snake_mu C P t Ab A B X D triple)) (@comp_fapp0 C _ _ _ (@comp_fapp0
          C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple
          cocone) (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone))
          (@comp_fapp0 C _ _ _ (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive C P
          t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone)
      (@abelian_snake_pi C P t Ab A B X D triple))))
≔ @preadditive_precompose_difference_right_zero_path C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone) (@comp_fapp0 C
      _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
      (@comp_fapp0 C _ _ _ (@abelian_snake_third_extension_pushout_factor C P t Ab A B X D T triple
      cocone) (@abelian_snake_q1 C P t Ab A B X D triple))) (@comp_fapp0 C _ _ _
      (@abelian_snake_third_gamma_extension_factor C P t Ab A B X D T triple cocone)
      (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
      (@abelian_snake_mu C P t Ab A B X D triple) (@comp_fapp0 C _ _ _ (@comp_fapp0 C _ _ _
      (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
      (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone)) (@comp_fapp0 C
      _ _ _ (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone)
      (@abelian_snake_pi C P t Ab A B X D triple)))
    (@abelian_snake_third_left_mu_path C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_right_mu_zero_path C P t Ab A B X D T triple cocone);
