/* Kernel-side maps of the generic six-term snake sequence. */

require open emdash.emdash3_2_abelian_snake_lemma;

symbol abelian_snake_beta_kernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalKernel C
      (@abelian_stability_preadditive C P t Ab) B X
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
≔ (@abelian_stability_kernels C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_ker_beta_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple);

symbol abelian_snake_k_beta
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B)
≔ @computational_kernel_morphism C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple);

symbol abelian_snake_beta_k_beta_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple) X)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_k_beta C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple) X))
≔ @computational_kernel_annihilation C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple);

symbol abelian_snake_alpha_kernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalKernel C
      (@abelian_stability_preadditive C P t Ab) A
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_alpha C P t Ab A B X D triple))
≔ (@abelian_stability_kernels C P t Ab) A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple);

symbol abelian_snake_ker_alpha_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@abelian_stability_preadditive C P t Ab) A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_kernel C P t Ab A B X D triple);

symbol abelian_snake_k_alpha
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) A)
≔ @computational_kernel_morphism C
    (@abelian_stability_preadditive C P t Ab) A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_kernel C P t Ab A B X D triple);

symbol abelian_snake_alpha_k_alpha_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_alpha C P t Ab A B X D triple)
        (@abelian_snake_k_alpha C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)))
≔ @computational_kernel_annihilation C
    (@abelian_stability_preadditive C P t Ab) A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_kernel C P t Ab A B X D triple);

symbol abelian_snake_delta_k_alpha_beta_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) X)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_k_alpha C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) X))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_k_alpha C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C A X)
        (Hom C
          (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) X)
        (λ h : τ (Hom C A X),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_k_alpha C P t Ab A B X D triple))
        _ _
        (@eq_sym _ _ _
          (@abelian_snake_alpha_path C P t Ab A B X D triple)))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_mu C P t Ab A B X D triple)
            (@abelian_snake_alpha C P t Ab A B X D triple)
            (@abelian_snake_k_alpha C P t Ab A B X D triple)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_ker_lambda_object C P t Ab A B X D triple))
            (Hom C
              (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) X)
            (λ h : τ (Hom C
                (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
                (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _
                (@abelian_snake_mu C P t Ab A B X D triple) h)
            _ _
            (@abelian_snake_alpha_k_alpha_zero_path C P t
              Ab A B X D triple))
          (@preadditive_comp_zero_right_path C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
            X
            (@abelian_snake_mu C P t Ab A B X D triple)))));

symbol abelian_snake_k_alpha_beta_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab) B X
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) B)
    (λ h : τ (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) B),
      @= (Hom C
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) X)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) X))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_k_alpha C P t Ab A B X D triple))
    (@abelian_snake_delta_k_alpha_beta_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_ker_alpha_to_ker_beta
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_k_alpha_beta_cone C P t Ab A B X D triple);

symbol abelian_snake_ker_alpha_to_ker_beta_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) B)
      (@comp_fapp0 C _ _ _
        (@computational_kernel_morphism C
          (@abelian_stability_preadditive C P t Ab) B X
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_beta_kernel C P t Ab A B X D triple))
        (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple))
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab) B X
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_k_alpha_beta_cone C P t Ab A B X D triple)))
≔ @computational_kernel_lift_path C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_k_alpha_beta_cone C P t Ab A B X D triple);

symbol abelian_snake_epsilon_k_beta_gamma_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple) D)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_epsilon C P t Ab A B X D triple)
          (@abelian_snake_k_beta C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple) D))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_gamma C P t Ab A B X D triple)
      (@abelian_snake_epsilon C P t Ab A B X D triple)
      (@abelian_snake_k_beta C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C B D)
        (Hom C
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple) D)
        (λ h : τ (Hom C B D),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_k_beta C P t Ab A B X D triple))
        _ _
        (@abelian_snake_gamma_path C P t Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_lambda C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)
            (@abelian_snake_beta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)
            (@abelian_snake_k_beta C P t Ab A B X D triple)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_ker_beta_object C P t Ab A B X D triple) X)
            (Hom C
              (@abelian_snake_ker_beta_object C P t Ab A B X D triple) D)
            (λ h : τ (Hom C
                (@abelian_snake_ker_beta_object C P t Ab A B X D triple) X),
              @comp_fapp0 C _ _ _
                (@abelian_snake_lambda C
                  (@abelian_stability_preadditive C P t Ab) A B X D triple) h)
            _ _
            (@abelian_snake_beta_k_beta_zero_path C P t
              Ab A B X D triple))
          (@preadditive_comp_zero_right_path C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
            X D
            (@abelian_snake_lambda C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)))));

symbol abelian_snake_k_beta_gamma_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
      (@abelian_snake_gamma C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
    (λ h : τ (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
      @= (Hom C
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple) D)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_gamma C P t Ab A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple) D))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_epsilon C P t Ab A B X D triple)
      (@abelian_snake_k_beta C P t Ab A B X D triple))
    (@abelian_snake_epsilon_k_beta_gamma_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_ker_beta_to_ker_gamma
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_kernel C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_k_beta_gamma_cone C P t Ab A B X D triple);

symbol abelian_snake_ker_beta_to_ker_gamma_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@computational_kernel_morphism C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
          (@abelian_snake_gamma C P t Ab A B X D triple)
          (@abelian_snake_gamma_kernel C P t Ab A B X D triple))
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_k_beta_gamma_cone C P t Ab A B X D triple)))
≔ @computational_kernel_lift_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_kernel C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_k_beta_gamma_cone C P t Ab A B X D triple);
