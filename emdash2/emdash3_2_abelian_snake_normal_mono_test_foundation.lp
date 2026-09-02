/* Cokernel evidence for the second snake normal test. */

require open emdash.emdash3_2_abelian_snake_normal_epi;
require open emdash.emdash3_2_abelian_snake_normal_mono_foundation;

symbol abelian_snake_q2_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalCokernel C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)
      (@abelian_snake_q2 C P t Ab A B X D triple))
≔ (@abelian_stability_cokernels C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple);

symbol abelian_snake_q2_cokernel_object
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
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@abelian_snake_q2_cokernel C P t Ab A B X D triple);

symbol abelian_snake_q2_cokernel_projection
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_pushout_object C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
≔ @computational_cokernel_morphism C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@abelian_snake_q2_cokernel C P t Ab A B X D triple);

symbol abelian_snake_q2_cokernel_annihilation
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
        (@abelian_snake_q2 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)))
≔ @computational_cokernel_annihilation C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@abelian_snake_q2_cokernel C P t Ab A B X D triple);

symbol abelian_snake_q2_cokernel_after_q1_mu_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
          (@abelian_snake_q1 C P t Ab A B X D triple))
        (@abelian_snake_mu C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
        (@abelian_snake_q1 C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _
            (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple) h)
        _ _
        (@abelian_snake_pushout_compatibility_path C P t
          Ab A B X D triple))
      (@eq_trans _ _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
          (@abelian_snake_q2 C P t Ab A B X D triple)
          (@abelian_snake_pi C P t Ab A B X D triple))
        (@eq_trans _ _ _ _
          (@eq_ap
            (Hom C
              (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
            (Hom C
              (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
              (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
            (λ h : τ (Hom C
                (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
                (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)),
              @comp_fapp0 C _ _ _ h
                (@abelian_snake_pi C P t Ab A B X D triple))
            _ _
            (@abelian_snake_q2_cokernel_annihilation C P t
              Ab A B X D triple))
          (@preadditive_comp_zero_left_path C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)
            (@abelian_snake_pi C P t Ab A B X D triple)))));

symbol abelian_snake_q2_cokernel_q1_after_beta_p2_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
          (@abelian_snake_q1 C P t Ab A B X D triple))
        (@weak_kernel_annihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          X D
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_beta_p2_lambda_cone C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)))
≔ @kernel_lift_postannihilation_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    X
    (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)
    (@computational_kernel_morphism C
      (@abelian_stability_preadditive C P t Ab)
      X D
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_lambda_kernel C P t Ab A B X D triple))
    (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple)
    (@weak_kernel_annihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      X D
      (@abelian_snake_lambda C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_beta_p2_lambda_cone C P t Ab A B X D triple))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
      (@abelian_snake_q1 C P t Ab A B X D triple))
    (@abelian_snake_beta_p2_lambda_lift_path C P t Ab A B X D triple)
    (@abelian_snake_q2_cokernel_after_q1_mu_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_q2_cokernel_middle_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
        (@abelian_snake_middle_arrow C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q1 C P t Ab A B X D triple)
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple))
      (@abelian_snake_p2 C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C B
          (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
        (λ h : τ (Hom C B
            (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_p2 C P t Ab A B X D triple))
        _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
          (@abelian_snake_q1 C P t Ab A B X D triple)
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comp_assoc C _ _ _ _
            (@comp_fapp0 C _ _ _
              (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
              (@abelian_snake_q1 C P t Ab A B X D triple))
            (@abelian_snake_beta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)
            (@abelian_snake_p2 C P t Ab A B X D triple)))
        (@abelian_snake_q2_cokernel_q1_after_beta_p2_zero_path C P t
          Ab A B X D triple)));
