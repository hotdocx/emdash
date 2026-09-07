/* Final pair of the six-term snake sequence. */

require open emdash.emdash3_2_abelian_snake_six_term_cokernel_zero;
require open emdash.emdash3_2_abelian_canonical_kernel_extensions;
require open emdash.emdash3_2_exactness_extensions_to_exact;

symbol abelian_snake_fourth_exact_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ
    (@ComputationalChainPair C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C
  (@abelian_stability_preadditive C P t Ab)
  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
  (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
  (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
  (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
  (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
  (@abelian_snake_cokernel_maps_zero_path C P t Ab A B X D triple);

symbol abelian_snake_fourth_exact_homology
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ
    (@ComputationalHomologyAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple))
≔ @computational_homology_at C P t
  (@abelian_stability_preabelian C P t Ab)
  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
  (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
  (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
  (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple);

symbol abelian_snake_fourth_psi_cbeta_mu_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (@=
      (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) T)
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@cokernel_coannihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
          (@abelian_snake_c_beta C P t Ab A B X D triple))
        (@abelian_snake_mu C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) T))
≔
  (@eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@cokernel_coannihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
        (@abelian_snake_c_beta C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
        (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) T)
        (λ h : τ
          (Hom C
            (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
          ,
          (@comp_fapp0 C _ _ _
            (@cokernel_coannihilator_arrow C
              (@abelian_stability_preadditive C P t Ab)
              (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
              (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
            h))
        _ _
        (@eq_sym _ _ _ (@abelian_snake_coker_alpha_to_coker_beta_path C P t Ab A B X D triple)))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@cokernel_coannihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
          (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
          (@abelian_snake_pi C P t Ab A B X D triple))
        (@preadditive_precompose_zero_path C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple) T
          (@comp_fapp0 C _ _ _
            (@cokernel_coannihilator_arrow C
              (@abelian_stability_preadditive C P t Ab)
              (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
              (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
            (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple))
          (@abelian_snake_pi C P t Ab A B X D triple)
          (@cokernel_coannihilator_path C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)))));

symbol abelian_snake_fourth_lambda_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (@CokernelCoannihilator C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X
      (@abelian_snake_mu C P t Ab A B X D triple) T)
≔ @Struct_sigma
  (Hom C X T)
  (λ h : τ
    (Hom C X T), @=
    (Hom C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) T)
    (@comp_fapp0 C _ _ _ h (@abelian_snake_mu C P t Ab A B X D triple))
    (@preadditive_hom_zero C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) T))
  (@comp_fapp0 C _ _ _
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
    (@abelian_snake_c_beta C P t Ab A B X D triple))
  (@abelian_snake_fourth_psi_cbeta_mu_zero_path C P t Ab A B X D T triple cocone);
