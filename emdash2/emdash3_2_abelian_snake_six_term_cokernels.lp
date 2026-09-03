/* Cokernel-side maps of the generic six-term snake sequence. */

require open emdash.emdash3_2_abelian_snake_six_term_kernels;
require open emdash.emdash3_2_abelian_snake_six_term_cokernel_beta_foundation;

symbol abelian_snake_gamma_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalCokernel C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
      (@abelian_snake_gamma C P t Ab A B X D triple))
≔ (@abelian_stability_cokernels C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
    (@abelian_snake_gamma C P t Ab A B X D triple);

symbol abelian_snake_coker_gamma_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_cokernel C P t Ab A B X D triple);

symbol abelian_snake_c_gamma
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C D
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
≔ @computational_cokernel_morphism C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_cokernel C P t Ab A B X D triple);

symbol abelian_snake_c_gamma_gamma_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_gamma C P t Ab A B X D triple)
        (@abelian_snake_gamma C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))
≔ @computational_cokernel_annihilation C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_cokernel C P t Ab A B X D triple);

symbol abelian_snake_c_gamma_lambda_beta_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C B
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_c_gamma C P t Ab A B X D triple)
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab) B
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_c_gamma C P t Ab A B X D triple)
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C B D)
        (Hom C B
          (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
        (λ h : τ (Hom C B D),
          @comp_fapp0 C _ _ _
            (@abelian_snake_c_gamma C P t Ab A B X D triple) h)
        _ _
        (@eq_sym _ _ _
          (@abelian_snake_gamma_path C P t Ab A B X D triple)))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_c_gamma C P t Ab A B X D triple)
          (@abelian_snake_gamma C P t Ab A B X D triple)
          (@abelian_snake_epsilon C P t Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
              (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
            (Hom C B
              (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
            (λ h : τ (Hom C
                (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
                (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_epsilon C P t Ab A B X D triple))
            _ _
            (@abelian_snake_c_gamma_gamma_zero_path C P t
              Ab A B X D triple))
          (@preadditive_comp_zero_left_path C
            (@abelian_stability_preadditive C P t Ab)
            B
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_epsilon C P t Ab A B X D triple)))));

symbol abelian_snake_beta_c_gamma_lambda_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@CokernelCoannihilator C
      (@abelian_stability_preadditive C P t Ab) B X
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C X
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
    (λ h : τ (Hom C X
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
      @= (Hom C B
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _ h
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab) B
          (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_c_gamma C P t Ab A B X D triple)
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
    (@abelian_snake_c_gamma_lambda_beta_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_coker_beta_to_coker_gamma
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
≔ @computational_cokernel_colift C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_cokernel C P t Ab A B X D triple)
    (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_beta_c_gamma_lambda_cocone C P t Ab A B X D triple);
symbol abelian_snake_coker_beta_to_coker_gamma_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C X
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
        (@computational_cokernel_morphism C
          (@abelian_stability_preadditive C P t Ab) B X
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_beta_cokernel C P t Ab A B X D triple)))
      (@cokernel_coannihilator_arrow C
        (@abelian_stability_preadditive C P t Ab) B X
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_beta_c_gamma_lambda_cocone C P t Ab A B X D triple)))
≔ @computational_cokernel_colift_path C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_cokernel C P t Ab A B X D triple)
    (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_beta_c_gamma_lambda_cocone C P t Ab A B X D triple);
