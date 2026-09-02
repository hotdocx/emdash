/* Whole selected-factor snapshot of the generic snake construction. */

require open emdash.emdash3_2_abelian_snake_connecting;

symbol AbelianSnakeConnectingResult
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : Grpd
≔ @Product_grpd
    (@NormalEpiColiftSpace C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_p1 C P t Ab A B X D triple)
      (@abelian_snake_p1_kernel C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)
      (@abelian_snake_p1_normal_epi_test C P t Ab A B X D triple))
    (@NormalMonoLiftSpace C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)
      (@abelian_snake_q2 C P t Ab A B X D triple)
      (@abelian_snake_q2_cokernel C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_q2_normal_mono_test C P t Ab A B X D triple));

symbol abelian_snake_connecting_result
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@AbelianSnakeConnectingResult C P t Ab A B X D triple)
≔ @Product_pair_grpd _ _
    (@Struct_sigma
      (Hom C
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_pushout_object C P t Ab A B X D triple))
      (λ v : τ (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple)),
        @= (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
          (@comp_fapp0 C _ _ _ v
            (@abelian_snake_p1 C P t Ab A B X D triple))
          (@cokernel_coannihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_p1_kernel_object C P t Ab A B X D triple)
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_p1_kernel_embedding C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple)
            (@abelian_snake_p1_normal_epi_test C P t Ab A B X D triple)))
      (@abelian_snake_u C P t Ab A B X D triple)
      (@abelian_snake_u_path C P t Ab A B X D triple))
    (@Struct_sigma
      (Hom C
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
      (λ v : τ (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)),
        @= (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
          (@comp_fapp0 C _ _ _
            (@abelian_snake_q2 C P t Ab A B X D triple) v)
          (@weak_kernel_annihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_pushout_object C P t Ab A B X D triple)
            (@abelian_snake_q2_cokernel_object C P t Ab A B X D triple)
            (@abelian_snake_q2_cokernel_projection C P t Ab A B X D triple)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_q2_normal_mono_test C P t Ab A B X D triple)))
      (@abelian_snake_connecting C P t Ab A B X D triple)
      (@abelian_snake_connecting_path C P t Ab A B X D triple));
