/* First snake normal test and the selected colift along p1. */

require open emdash.emdash3_2_abelian_snake_normal_epi_foundation;

symbol abelian_snake_q1_beta_after_p2_kernel_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@cokernel_coannihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple)
          (@abelian_snake_q1_beta_delta_cocone C P t Ab A B X D triple))
        (@weak_kernel_annihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          B (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
          (@abelian_snake_epsilon C P t Ab A B X D triple)
          (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
          (@abelian_snake_p2_kernel_epsilon_cone C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)))
≔ @computational_image_factor_annihilated_by_cocone C P t
    (@abelian_stability_preabelian C P t Ab)
    A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
    (@abelian_snake_p2_kernel_epsilon_cone C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q1_beta_delta_cocone C P t Ab A B X D triple);

symbol abelian_snake_middle_kernel_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_middle_arrow C P t Ab A B X D triple)
        (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_q1 C P t Ab A B X D triple)
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@abelian_snake_p2 C P t Ab A B X D triple)
        (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple)))
    (@abelian_snake_q1_beta_after_p2_kernel_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_p1_normal_epi_test
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@NormalEpiTest C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_p1 C P t Ab A B X D triple)
      (@abelian_snake_p1_kernel C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
    (λ h : τ (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)),
      @= (Hom C
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _ h
          (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple)))
    (@abelian_snake_middle_arrow C P t Ab A B X D triple)
    (@abelian_snake_middle_kernel_zero_path C P t Ab A B X D triple);

symbol abelian_snake_u
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
≔ @colift_along_epimorphism C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_stability_kernels C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_epic C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_p1_normal_epi_test C P t Ab A B X D triple);

symbol abelian_snake_u_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_u C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@cokernel_coannihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)
        (@abelian_snake_p1_normal_epi_test C P t Ab A B X D triple)))
≔ @colift_along_epimorphism_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_stability_kernels C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_epic C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_p1_normal_epi_test C P t Ab A B X D triple);
