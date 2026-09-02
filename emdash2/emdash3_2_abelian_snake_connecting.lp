/* Final generic CAP-style snake connecting arrow. */

require open emdash.emdash3_2_abelian_snake_normal_mono_test_foundation;

symbol abelian_snake_q2_cokernel_u_after_p1_zero_path
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
          (@abelian_snake_u C P t Ab A B X D triple))
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
        (@abelian_snake_u C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple)))
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _
            (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple) h)
        _ _
        (@abelian_snake_u_path C P t Ab A B X D triple))
      (@abelian_snake_q2_cokernel_middle_zero_path C P t
        Ab A B X D triple));

symbol abelian_snake_q2_cokernel_u_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
        (@abelian_snake_u C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)))
≔ (@abelian_snake_p1_epic C P t Ab A B X D triple)
    (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
      (@abelian_snake_u C P t Ab A B X D triple))
    (@preadditive_hom_zero C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
    (@eq_trans _ _ _ _
      (@abelian_snake_q2_cokernel_u_after_p1_zero_path C P t
        Ab A B X D triple)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_left_path C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)
          (@abelian_snake_p1 C P t Ab A B X D triple))));

symbol abelian_snake_q2_normal_mono_test
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@NormalMonoTest C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)
      (@abelian_snake_q2 C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
    (λ h : τ (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)),
      @= (Hom C
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _
          (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)))
    (@abelian_snake_u C P t Ab A B X D triple)
    (@abelian_snake_q2_cokernel_u_zero_path C P t Ab A B X D triple);

symbol abelian_snake_connecting
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
≔ @lift_along_monomorphism C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_stability_cokernels C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@abelian_snake_q2_monic C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_q2_normal_mono_test C P t Ab A B X D triple);

symbol abelian_snake_connecting_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q2 C P t Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple))
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_pushout_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)
        (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_q2_normal_mono_test C P t Ab A B X D triple)))
≔ @lift_along_monomorphism_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_stability_cokernels C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@abelian_snake_q2_monic C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_q2_normal_mono_test C P t Ab A B X D triple);
