/* Reconstruction of the left coextension after mu. */

require open emdash.emdash3_2_abelian_snake_exact_third_cokernel_factor;

symbol abelian_snake_third_left_mu_path
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
    _ _ (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T
    triple cocone) (@comp_fapp0 C _ _ _ (@abelian_snake_third_extension_pushout_factor C P t Ab A B
    X D T triple cocone) (@abelian_snake_q1 C P t Ab A B X D triple))) (@abelian_snake_mu C P t Ab A
    B X D triple)) (@comp_fapp0 C _ _ _ (@comp_fapp0 C _ _ _
    (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone)) (@comp_fapp0 C _
    _ _ (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone)
      (@abelian_snake_pi C P t Ab A B X D triple))))
≔ (@eq_trans _ _ _ _
    (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t
      Ab A B X D T triple cocone) (@comp_fapp0 C _ _ _
      (@abelian_snake_third_extension_pushout_factor C P t Ab A B X D T triple cocone)
      (@abelian_snake_q1 C P t Ab A B X D triple)) (@abelian_snake_mu C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
    (@eq_ap (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)) (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (λ h : τ (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)), (@comp_fapp0 C _
        _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone) h))
        _ _ (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ (@abelian_snake_third_extension_pushout_factor C P
        t Ab A B X D T triple cocone) (@abelian_snake_q1 C P t Ab A B X D triple) (@abelian_snake_mu
        C P t Ab A B X D triple))))
    (@eq_trans _ _ _ _
    (@eq_ap (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)) (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (λ h : τ (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)), (@comp_fapp0 C _ _ _
        (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
        (@comp_fapp0 C _ _ _ (@abelian_snake_third_extension_pushout_factor C P t Ab A B X D T
        triple cocone) h))) _ _ (@abelian_snake_pushout_compatibility_path C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
    (@eq_ap (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)) (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (λ h : τ (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)), (@comp_fapp0 C _
        _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone) h))
        _ _ (@comp_assoc C _ _ _ _ (@abelian_snake_third_extension_pushout_factor C P t Ab A B X D T
        triple cocone) (@abelian_snake_q2 C P t Ab A B X D triple) (@abelian_snake_pi C P t Ab A B X
        D triple)))
    (@eq_trans _ _ _ _
    (@eq_ap (Hom C (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)) (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (λ h : τ (Hom C (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)), (@comp_fapp0 C _
        _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
        (@comp_fapp0 C _ _ _ h (@abelian_snake_pi C P t Ab A B X D triple)))) _ _
        (@abelian_snake_third_extension_path C P t Ab A B X D T triple cocone))
    (@eq_trans _ _ _ _
    (@eq_ap (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)) (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (λ h : τ (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)), (@comp_fapp0 C _
        _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone) h))
        _ _ (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ (@abelian_snake_third_extension_monomorphism C P t
        Ab A B X D T triple cocone) (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive
        C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone)
      (@abelian_snake_pi C P t Ab A B X D triple))))
    (@comp_assoc C _ _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T
      triple cocone) (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone)
      (@comp_fapp0 C _ _ _ (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive C P t
      Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone)
      (@abelian_snake_pi C P t Ab A B X D triple)))))))));
