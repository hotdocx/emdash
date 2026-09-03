/* Coker(beta) and the induced Coker(alpha) -> Coker(beta) map. */

require open emdash.emdash3_2_abelian_snake_lemma;

symbol abelian_snake_beta_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalCokernel C
      (@abelian_stability_preadditive C P t Ab) B X
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
≔ (@abelian_stability_cokernels C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple);

symbol abelian_snake_coker_beta_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_cokernel C P t Ab A B X D triple);

symbol abelian_snake_c_beta
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C X
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ @computational_cokernel_morphism C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_cokernel C P t Ab A B X D triple);

symbol abelian_snake_c_beta_beta_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C B
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_beta C P t Ab A B X D triple)
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab) B
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ @computational_cokernel_annihilation C
    (@abelian_stability_preadditive C P t Ab) B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_cokernel C P t Ab A B X D triple);

symbol abelian_snake_c_beta_mu_alpha_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C A
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_c_beta C P t Ab A B X D triple)
          (@abelian_snake_mu C P t Ab A B X D triple))
        (@abelian_snake_alpha C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab) A
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_c_beta C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_alpha C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C A X)
        (Hom C A
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
        (λ h : τ (Hom C A X),
          @comp_fapp0 C _ _ _
            (@abelian_snake_c_beta C P t Ab A B X D triple) h)
        _ _
        (@abelian_snake_alpha_path C P t Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_c_beta C P t Ab A B X D triple)
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C B
              (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
            (Hom C A
              (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
            (λ h : τ (Hom C B
                (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_delta C
                  (@abelian_stability_preadditive C P t Ab) A B X D triple))
            _ _
            (@abelian_snake_c_beta_beta_zero_path C P t
              Ab A B X D triple))
          (@preadditive_comp_zero_left_path C
            (@abelian_stability_preadditive C P t Ab)
            A B
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_delta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)))));

symbol abelian_snake_alpha_c_beta_mu_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@CokernelCoannihilator C
      (@abelian_stability_preadditive C P t Ab) A
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_alpha C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
    (λ h : τ (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
      @= (Hom C A
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _ h
          (@abelian_snake_alpha C P t Ab A B X D triple))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab) A
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_c_beta C P t Ab A B X D triple)
      (@abelian_snake_mu C P t Ab A B X D triple))
    (@abelian_snake_c_beta_mu_alpha_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_coker_alpha_to_coker_beta
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ @computational_cokernel_colift C
    (@abelian_stability_preadditive C P t Ab) A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_cokernel C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_alpha_c_beta_mu_cocone C P t Ab A B X D triple);

symbol abelian_snake_coker_alpha_to_coker_beta_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
        (@computational_cokernel_morphism C
          (@abelian_stability_preadditive C P t Ab) A
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_alpha C P t Ab A B X D triple)
          (@abelian_snake_alpha_cokernel C P t Ab A B X D triple)))
      (@cokernel_coannihilator_arrow C
        (@abelian_stability_preadditive C P t Ab) A
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_alpha C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_alpha_c_beta_mu_cocone C P t Ab A B X D triple)))
≔ @computational_cokernel_colift_path C
    (@abelian_stability_preadditive C P t Ab) A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_cokernel C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_alpha_c_beta_mu_cocone C P t Ab A B X D triple);
