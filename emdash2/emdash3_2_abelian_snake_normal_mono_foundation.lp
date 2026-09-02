/* Canonical lambda-kernel evidence for the second snake normal test. */

require open emdash.emdash3_2_abelian_snake_normal_epi_foundation;

symbol abelian_snake_beta_p2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple) X)
≔ @comp_fapp0 C _ _ _
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_p2 C P t Ab A B X D triple);

symbol abelian_snake_gamma_epsilon_p2_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple) D)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_epsilon C P t Ab A B X D triple)
          (@abelian_snake_p2 C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple) D))
≔ @fiber_product_right_annihilation_path C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    B D
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple)
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_iota_zero_path C P t Ab A B X D triple);

symbol abelian_snake_beta_p2_lambda_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple) D)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_beta_p2 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple) D))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_p2 C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C B D)
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple) D)
        (λ h : τ (Hom C B D),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_p2 C P t Ab A B X D triple))
        _ _
        (@eq_sym _ _ _
          (@abelian_snake_gamma_path C P t Ab A B X D triple)))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_gamma C P t Ab A B X D triple)
            (@abelian_snake_epsilon C P t Ab A B X D triple)
            (@abelian_snake_p2 C P t Ab A B X D triple)))
        (@abelian_snake_gamma_epsilon_p2_zero_path C P t
          Ab A B X D triple)));

symbol abelian_snake_beta_p2_lambda_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      X D
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_fiber_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C (@abelian_snake_fiber_object C P t Ab A B X D triple) X)
    (λ h : τ (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple) X),
      @= (Hom C
        (@abelian_snake_fiber_object C P t Ab A B X D triple) D)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_fiber_object C P t Ab A B X D triple) D))
    (@abelian_snake_beta_p2 C P t Ab A B X D triple)
    (@abelian_snake_beta_p2_lambda_zero_path C P t Ab A B X D triple);

symbol abelian_snake_beta_p2_lambda_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab)
    X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_lambda_kernel C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_beta_p2_lambda_cone C P t Ab A B X D triple);

symbol abelian_snake_beta_p2_lambda_lift_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple) X)
      (@comp_fapp0 C _ _ _
        (@computational_kernel_morphism C
          (@abelian_stability_preadditive C P t Ab)
          X D
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_lambda_kernel C P t Ab A B X D triple))
        (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple))
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        X D
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_beta_p2_lambda_cone C P t Ab A B X D triple)))
≔ @computational_kernel_lift_path C
    (@abelian_stability_preadditive C P t Ab)
    X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_lambda_kernel C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_beta_p2_lambda_cone C P t Ab A B X D triple);
