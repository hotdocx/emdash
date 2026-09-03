/*
  Generic computational Abelian snake connecting construction.

  A composable triple A --delta--> B --beta--> C --lambda--> D with
  lambda o beta o delta = 0 determines the CAP kernel/cokernel diagram.
  Every intermediate arrow below is selected by the existing universal
  operations. The final normal-epi and normal-mono tests are derived from the
  same internal paths; no split epimorphism or manual diagram is stored.
*/

require open emdash.emdash3_2_abelian_fiber_pushout_stability;

symbol AbelianSnakeTriple
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  (A B X D : τ (Obj C))
  : Grpd
≔ `Σ_ delta : τ (Hom C A B),
   `Σ_ beta : τ (Hom C B X),
   `Σ_ lambda : τ (Hom C X D),
     @= (Hom C A D)
       (@comp_fapp0 C A X D lambda
         (@comp_fapp0 C A B X beta delta))
       (@preadditive_hom_zero C S A D);

symbol abelian_snake_triple_intro
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X D : τ (Obj C)]
  (delta : τ (Hom C A B))
  (beta : τ (Hom C B X))
  (lambda : τ (Hom C X D))
  (zero : τ (@= (Hom C A D)
    (@comp_fapp0 C A X D lambda
      (@comp_fapp0 C A B X beta delta))
    (@preadditive_hom_zero C S A D)))
  : τ (@AbelianSnakeTriple C S A B X D)
≔ @Struct_sigma (Hom C A B)
    (λ delta0 : τ (Hom C A B),
      `Σ_ beta0 : τ (Hom C B X),
      `Σ_ lambda0 : τ (Hom C X D),
        @= (Hom C A D)
          (@comp_fapp0 C A X D lambda0
            (@comp_fapp0 C A B X beta0 delta0))
          (@preadditive_hom_zero C S A D))
    delta
    (@Struct_sigma (Hom C B X)
      (λ beta0 : τ (Hom C B X),
        `Σ_ lambda0 : τ (Hom C X D),
          @= (Hom C A D)
            (@comp_fapp0 C A X D lambda0
              (@comp_fapp0 C A B X beta0 delta))
            (@preadditive_hom_zero C S A D))
      beta
      (@Struct_sigma (Hom C X D)
        (λ lambda0 : τ (Hom C X D),
          @= (Hom C A D)
            (@comp_fapp0 C A X D lambda0
              (@comp_fapp0 C A B X beta delta))
            (@preadditive_hom_zero C S A D))
        lambda zero));

symbol abelian_snake_delta
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C S A B X D))
  : τ (Hom C A B)
≔ sigma_Fst triple;

symbol abelian_snake_beta
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C S A B X D))
  : τ (Hom C B X)
≔ sigma_Fst (sigma_Snd triple);

symbol abelian_snake_lambda
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C S A B X D))
  : τ (Hom C X D)
≔ sigma_Fst (sigma_Snd (sigma_Snd triple));

symbol abelian_snake_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C S A B X D))
  : τ (@= (Hom C A D)
      (@comp_fapp0 C A X D
        (@abelian_snake_lambda C S A B X D triple)
        (@comp_fapp0 C A B X
          (@abelian_snake_beta C S A B X D triple)
          (@abelian_snake_delta C S A B X D triple)))
      (@preadditive_hom_zero C S A D))
≔ sigma_Snd (sigma_Snd (sigma_Snd triple));

symbol abelian_snake_lambda_beta
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C S A B X D))
  : τ (Hom C B D)
≔ @comp_fapp0 C B X D
    (@abelian_snake_lambda C S A B X D triple)
    (@abelian_snake_beta C S A B X D triple);

symbol abelian_snake_beta_delta
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C S A B X D))
  : τ (Hom C A X)
≔ @comp_fapp0 C A B X
    (@abelian_snake_beta C S A B X D triple)
    (@abelian_snake_delta C S A B X D triple);

// lambda beta is coannihilated by delta.
symbol abelian_snake_gamma_cone
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
      D)
≔ @Struct_sigma (Hom C B D)
    (λ h : τ (Hom C B D),
      @= (Hom C A D)
        (@comp_fapp0 C A B D h
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab) A D))
    (@abelian_snake_lambda_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@eq_trans (Hom C A D) _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C A B X D
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)))
      (@abelian_snake_zero_path C
        (@abelian_stability_preadditive C P t Ab) A B X D triple));

symbol abelian_snake_delta_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalCokernel C
      (@abelian_stability_preadditive C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
≔ (@abelian_stability_cokernels C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_epsilon
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C B
      (@computational_cokernel_object C
        (@abelian_stability_preadditive C P t Ab) A B
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_delta_cokernel C P t Ab A B X D triple)))
≔ @computational_cokernel_morphism C
    (@abelian_stability_preadditive C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_delta_cokernel C P t Ab A B X D triple);

symbol abelian_snake_gamma
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@computational_cokernel_object C
        (@abelian_stability_preadditive C P t Ab) A B
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D)
≔ @computational_cokernel_colift C
    (@abelian_stability_preadditive C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_delta_cokernel C P t Ab A B X D triple)
    D (@abelian_snake_gamma_cone C P t Ab A B X D triple);

symbol abelian_snake_gamma_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C B D)
      (@comp_fapp0 C B
        (@computational_cokernel_object C
          (@abelian_stability_preadditive C P t Ab) A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple))
      (@abelian_snake_lambda_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
≔ @computational_cokernel_colift_path C
    (@abelian_stability_preadditive C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_delta_cokernel C P t Ab A B X D triple)
    D (@abelian_snake_gamma_cone C P t Ab A B X D triple);

symbol abelian_snake_gamma_kernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalKernel C
      (@abelian_stability_preadditive C P t Ab)
      (@computational_cokernel_object C
        (@abelian_stability_preadditive C P t Ab) A B
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
      (@abelian_snake_gamma C P t Ab A B X D triple))
≔ (@abelian_stability_kernels C P t Ab)
    (@computational_cokernel_object C
      (@abelian_stability_preadditive C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
    (@abelian_snake_gamma C P t Ab A B X D triple);

symbol abelian_snake_iota
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab)
        (@computational_cokernel_object C
          (@abelian_stability_preadditive C P t Ab) A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_gamma_kernel C P t Ab A B X D triple))
      (@computational_cokernel_object C
        (@abelian_stability_preadditive C P t Ab) A B
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_delta_cokernel C P t Ab A B X D triple)))
≔ @computational_kernel_morphism C
    (@abelian_stability_preadditive C P t Ab)
    (@computational_cokernel_object C
      (@abelian_stability_preadditive C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_kernel C P t Ab A B X D triple);

// The readable iota observation retains its selected-kernel annihilation.
symbol abelian_snake_gamma_iota_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab)
        (@computational_cokernel_object C
          (@abelian_stability_preadditive C P t Ab) A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_gamma_kernel C P t Ab A B X D triple)) D)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_iota C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab)
          (@computational_cokernel_object C
            (@abelian_stability_preadditive C P t Ab) A B
            (@abelian_snake_delta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)
            (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
          (@abelian_snake_gamma C P t Ab A B X D triple)
          (@abelian_snake_gamma_kernel C P t Ab A B X D triple)) D))
≔ @computational_kernel_annihilation C
    (@abelian_stability_preadditive C P t Ab)
    (@computational_cokernel_object C
      (@abelian_stability_preadditive C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_kernel C P t Ab A B X D triple);

symbol abelian_snake_lambda_kernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalKernel C
      (@abelian_stability_preadditive C P t Ab) X D
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
≔ (@abelian_stability_kernels C P t Ab) X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_mu
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) X D
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_lambda_kernel C P t Ab A B X D triple)) X)
≔ @computational_kernel_morphism C
    (@abelian_stability_preadditive C P t Ab) X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_lambda_kernel C P t Ab A B X D triple);

// beta delta is annihilated by lambda.
symbol abelian_snake_alpha_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab) X D
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      A)
≔ @Struct_sigma (Hom C A X)
    (λ h : τ (Hom C A X),
      @= (Hom C A D)
        (@comp_fapp0 C A X D
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab) A D))
    (@abelian_snake_beta_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_zero_path C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_alpha
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C A
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) X D
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_lambda_kernel C P t Ab A B X D triple)))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab) X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_lambda_kernel C P t Ab A B X D triple)
    A (@abelian_snake_alpha_cone C P t Ab A B X D triple);

symbol abelian_snake_alpha_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C A X)
      (@comp_fapp0 C A
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab) X D
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_lambda_kernel C P t Ab A B X D triple)) X
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_alpha C P t Ab A B X D triple))
      (@abelian_snake_beta_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
≔ @computational_kernel_lift_path C
    (@abelian_stability_preadditive C P t Ab) X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_lambda_kernel C P t Ab A B X D triple)
    A (@abelian_snake_alpha_cone C P t Ab A B X D triple);

symbol abelian_snake_alpha_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalCokernel C
      (@abelian_stability_preadditive C P t Ab) A
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) X D
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_lambda_kernel C P t Ab A B X D triple))
      (@abelian_snake_alpha C P t Ab A B X D triple))
≔ (@abelian_stability_cokernels C P t Ab) A
    (@computational_kernel_object C
      (@abelian_stability_preadditive C P t Ab) X D
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_lambda_kernel C P t Ab A B X D triple))
    (@abelian_snake_alpha C P t Ab A B X D triple);

symbol abelian_snake_pi
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) X D
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_lambda_kernel C P t Ab A B X D triple))
      (@computational_cokernel_object C
        (@abelian_stability_preadditive C P t Ab) A
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab) X D
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_lambda_kernel C P t Ab A B X D triple))
        (@abelian_snake_alpha C P t Ab A B X D triple)
        (@abelian_snake_alpha_cokernel C P t Ab A B X D triple)))
≔ @computational_cokernel_morphism C
    (@abelian_stability_preadditive C P t Ab) A
    (@computational_kernel_object C
      (@abelian_stability_preadditive C P t Ab) X D
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_lambda_kernel C P t Ab A B X D triple))
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_cokernel C P t Ab A B X D triple);

// Readable endpoint aliases for the second CAP stage.
symbol abelian_snake_coker_delta_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@abelian_stability_preadditive C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_delta_cokernel C P t Ab A B X D triple);

symbol abelian_snake_ker_gamma_object
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
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_kernel C P t Ab A B X D triple);

symbol abelian_snake_ker_lambda_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@abelian_stability_preadditive C P t Ab) X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_lambda_kernel C P t Ab A B X D triple);

symbol abelian_snake_coker_alpha_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@abelian_stability_preadditive C P t Ab) A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_cokernel C P t Ab A B X D triple);

// FiberProduct(iota,epsilon).
symbol abelian_snake_fiber_product
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalFiberProduct C P t
      (@abelian_stability_additive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      B
      (@abelian_snake_iota C P t Ab A B X D triple)
      (@abelian_snake_epsilon C P t Ab A B X D triple))
≔ @abelian_selected_fiber_product C P t Ab
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple);

symbol abelian_snake_p1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_fiber_product C P t Ab A B X D triple))
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
≔ @computational_fiber_product_proj1 C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple);

symbol abelian_snake_p2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_fiber_product C P t Ab A B X D triple)) B)
≔ @computational_fiber_product_proj2 C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple);

symbol abelian_snake_epsilon_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@IsEpic C B
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_epsilon C P t Ab A B X D triple))
≔ @computational_cokernel_morphism_is_epic C
    (@abelian_stability_preadditive C P t Ab) A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_delta_cokernel C P t Ab A B X D triple);

symbol abelian_snake_p1_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@IsEpic C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_fiber_product C P t Ab A B X D triple))
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_p1 C P t Ab A B X D triple))
≔ @abelian_fiber_product_epic_projection C P t Ab
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_epsilon_epic C P t Ab A B X D triple);

// Pushout(mu,pi).
symbol abelian_snake_pushout
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalPushout C P t
      (@abelian_stability_additive C P t Ab)
      X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_mu C P t Ab A B X D triple)
      (@abelian_snake_pi C P t Ab A B X D triple))
≔ @abelian_selected_pushout C P t Ab
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    X (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple);

// Readable object projection of the selected fiber product.
symbol abelian_snake_fiber_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_fiber_product_object C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple);

// Readable object projection of the selected pushout.
symbol abelian_snake_pushout_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_pushout_object C P t
    (@abelian_stability_additive C P t Ab)
    X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_pushout C P t Ab A B X D triple);

symbol abelian_snake_q1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C X
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t Ab)
        X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_pushout C P t Ab A B X D triple)))
≔ @computational_pushout_inj1 C P t
    (@abelian_stability_additive C P t Ab)
    X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_pushout C P t Ab A B X D triple);

symbol abelian_snake_q2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t Ab)
        X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_pushout C P t Ab A B X D triple)))
≔ @computational_pushout_inj2 C P t
    (@abelian_stability_additive C P t Ab)
    X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_pushout C P t Ab A B X D triple);

symbol abelian_snake_mu_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@IsMonic C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X
      (@abelian_snake_mu C P t Ab A B X D triple))
≔ @computational_kernel_morphism_is_monic C
    (@abelian_stability_preadditive C P t Ab) X D
    (@abelian_snake_lambda C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_lambda_kernel C P t Ab A B X D triple);

symbol abelian_snake_q2_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@IsMonic C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t Ab)
        X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_pushout C P t Ab A B X D triple))
      (@abelian_snake_q2 C P t Ab A B X D triple))
≔ @abelian_pushout_monic_injection C P t Ab
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_mu_monic C P t Ab A B X D triple);
