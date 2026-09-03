/* Canonical fiber/image evidence for the first snake normal test. */

require open emdash.emdash3_2_abelian_snake_lemma;
require open emdash.emdash3_2_abelian_images;

symbol abelian_snake_middle_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
≔ @comp_fapp0 C _ _ _
    (@comp_fapp0 C _ _ _
      (@abelian_snake_q1 C P t Ab A B X D triple)
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
    (@abelian_snake_p2 C P t Ab A B X D triple);

// Selected kernel of p1.
symbol abelian_snake_p1_kernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalKernel C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_p1 C P t Ab A B X D triple))
≔ (@abelian_stability_kernels C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_p1 C P t Ab A B X D triple);

symbol abelian_snake_p1_kernel_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_kernel C P t Ab A B X D triple);

symbol abelian_snake_p1_kernel_embedding
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
      (@abelian_snake_fiber_object C P t Ab A B X D triple))
≔ @computational_kernel_morphism C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_kernel C P t Ab A B X D triple);

symbol abelian_snake_p1_kernel_annihilation
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_p1 C P t Ab A B X D triple)
        (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)))
≔ @computational_kernel_annihilation C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_kernel C P t Ab A B X D triple);

// Image(delta) is the selected kernel of epsilon.
symbol abelian_snake_delta_image
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalKernel C
      (@abelian_stability_preadditive C P t Ab)
      B
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_epsilon C P t Ab A B X D triple))
≔ @computational_image C P t
    (@abelian_stability_preabelian C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_delta_image_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_image_object C P t
    (@abelian_stability_preabelian C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_delta_image_embedding
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_delta_image_object C P t Ab A B X D triple) B)
≔ @computational_image_embedding C P t
    (@abelian_stability_preabelian C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_fiber_compatibility_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_p2 C P t Ab A B X D triple)))
≔ @computational_fiber_product_compatibility_path C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple);

// The second projection restricted to Ker(p1) is annihilated by epsilon.
symbol abelian_snake_p2_kernel_epsilon_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_p2 C P t Ab A B X D triple)
          (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_epsilon C P t Ab A B X D triple)
      (@abelian_snake_p2 C P t Ab A B X D triple)
      (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple))
        _ _
        (@eq_sym _ _ _
          (@abelian_snake_fiber_compatibility_path C P t
            Ab A B X D triple)))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@abelian_snake_iota C P t Ab A B X D triple)
            (@abelian_snake_p1 C P t Ab A B X D triple)
            (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple)))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
              (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
            (Hom C
              (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
            (λ h : τ (Hom C
                (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _
                (@abelian_snake_iota C P t Ab A B X D triple) h)
            _ _
            (@abelian_snake_p1_kernel_annihilation C P t
              Ab A B X D triple))
          (@preadditive_comp_zero_right_path C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
            (@abelian_snake_iota C P t Ab A B X D triple)))));

symbol abelian_snake_p2_kernel_epsilon_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      B (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_epsilon C P t Ab A B X D triple)
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple) B)
    (λ h : τ (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple) B),
      @= (Hom C
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _
          (@abelian_snake_epsilon C P t Ab A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple)))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_p2 C P t Ab A B X D triple)
      (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple))
    (@abelian_snake_p2_kernel_epsilon_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_p2_kernel_image_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
      (@abelian_snake_delta_image_object C P t Ab A B X D triple))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab)
    B (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_delta_image C P t Ab A B X D triple)
    (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
    (@abelian_snake_p2_kernel_epsilon_cone C P t Ab A B X D triple);

symbol abelian_snake_p2_kernel_image_lift_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple) B)
      (@comp_fapp0 C _ _ _
        (@computational_kernel_morphism C
          (@abelian_stability_preadditive C P t Ab)
          B (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
          (@abelian_snake_epsilon C P t Ab A B X D triple)
          (@abelian_snake_delta_image C P t Ab A B X D triple))
        (@abelian_snake_p2_kernel_image_lift C P t Ab A B X D triple))
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        B (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_p2_kernel_epsilon_cone C P t Ab A B X D triple)))
≔ @computational_kernel_lift_path C
    (@abelian_stability_preadditive C P t Ab)
    B (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_delta_image C P t Ab A B X D triple)
    (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
    (@abelian_snake_p2_kernel_epsilon_cone C P t Ab A B X D triple);

symbol abelian_snake_pushout_compatibility_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q1 C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q2 C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)))
≔ @computational_pushout_compatibility_path C P t
    (@abelian_stability_additive C P t Ab)
    X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_pushout C P t Ab A B X D triple);

symbol abelian_snake_q1_beta
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C B
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
≔ @comp_fapp0 C _ _ _
    (@abelian_snake_q1 C P t Ab A B X D triple)
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

// q1 beta coannihilates delta by the alpha reconstruction and pushout law.
symbol abelian_snake_q1_beta_delta_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C A
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q1_beta C P t Ab A B X D triple)
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab) A
        (@abelian_snake_pushout_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_q1 C P t Ab A B X D triple)
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C A X)
        (Hom C A
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (λ h : τ (Hom C A X),
          @comp_fapp0 C _ _ _
            (@abelian_snake_q1 C P t Ab A B X D triple) h)
        _ _
        (@eq_sym _ _ _
          (@abelian_snake_alpha_path C P t Ab A B X D triple)))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_q1 C P t Ab A B X D triple)
          (@abelian_snake_mu C P t Ab A B X D triple)
          (@abelian_snake_alpha C P t Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
              (@abelian_snake_pushout_object C P t Ab A B X D triple))
            (Hom C A
              (@abelian_snake_pushout_object C P t Ab A B X D triple))
            (λ h : τ (Hom C
                (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
                (@abelian_snake_pushout_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_alpha C P t Ab A B X D triple))
            _ _
            (@abelian_snake_pushout_compatibility_path C P t
              Ab A B X D triple))
          (@eq_trans _ _ _ _
            (@eq_sym _ _ _
              (@comp_assoc C _ _ _ _
                (@abelian_snake_q2 C P t Ab A B X D triple)
                (@abelian_snake_pi C P t Ab A B X D triple)
                (@abelian_snake_alpha C P t Ab A B X D triple)))
            (@eq_trans _ _ _ _
              (@eq_ap
                (Hom C A
                  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
                (Hom C A
                  (@abelian_snake_pushout_object C P t Ab A B X D triple))
                (λ h : τ (Hom C A
                    (@abelian_snake_coker_alpha_object C P t
                      Ab A B X D triple)),
                  @comp_fapp0 C _ _ _
                    (@abelian_snake_q2 C P t Ab A B X D triple) h)
                _ _
                (@computational_cokernel_annihilation C
                  (@abelian_stability_preadditive C P t Ab)
                  A
                  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
                  (@abelian_snake_alpha C P t Ab A B X D triple)
                  (@abelian_snake_alpha_cokernel C P t Ab A B X D triple)))
              (@preadditive_comp_zero_right_path C
                (@abelian_stability_preadditive C P t Ab)
                A
                (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                (@abelian_snake_pushout_object C P t Ab A B X D triple)
                (@abelian_snake_q2 C P t Ab A B X D triple)))))));

symbol abelian_snake_q1_beta_delta_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@CokernelCoannihilator C
      (@abelian_stability_preadditive C P t Ab)
      A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C B (@abelian_snake_pushout_object C P t Ab A B X D triple))
    (λ h : τ (Hom C B
      (@abelian_snake_pushout_object C P t Ab A B X D triple)),
      @= (Hom C A
        (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _ h
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab) A
          (@abelian_snake_pushout_object C P t Ab A B X D triple)))
    (@abelian_snake_q1_beta C P t Ab A B X D triple)
    (@abelian_snake_q1_beta_delta_zero_path C P t Ab A B X D triple);

symbol abelian_snake_q1_beta_image_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_delta_image_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@cokernel_coannihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple)
          (@abelian_snake_q1_beta_delta_cocone C P t Ab A B X D triple))
        (@computational_image_embedding C P t
          (@abelian_stability_preabelian C P t Ab) A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_delta_image_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)))
≔ @computational_image_coannihilates_cocone C P t
    (@abelian_stability_preabelian C P t Ab)
    A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q1_beta_delta_cocone C P t Ab A B X D triple);
