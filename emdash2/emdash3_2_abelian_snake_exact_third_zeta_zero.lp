/* The canonical kernel-row cocone zeta kills iota. */

require open emdash.emdash3_2_abelian_snake_exact_third_su_path;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_third_m_psi_partial_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_third_extension_monomorphism C P t
          Ab A B X D T triple cocone)
        (@comp_fapp0 C _ _ _
          (@cokernel_coannihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_connecting C P t Ab A B X D triple)
            T cocone)
          (@abelian_snake_connecting C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t
          Ab A B X D T triple cocone)))
≔ @preadditive_postcompose_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    T
    (@abelian_snake_third_extension_object C P t
      Ab A B X D T triple cocone)
    (@abelian_snake_third_extension_monomorphism C P t
      Ab A B X D T triple cocone)
    (@comp_fapp0 C _ _ _
      (@cokernel_coannihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple)
        T cocone)
      (@abelian_snake_connecting C P t Ab A B X D triple))
    (@cokernel_coannihilator_path C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cocone);

symbol abelian_snake_third_zeta_iota_after_p1_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_third_zeta C P t
            Ab A B X D T triple cocone)
          (@abelian_snake_iota C P t Ab A B X D triple))
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t
          Ab A B X D T triple cocone)))
≔ @eq_trans _ _ _ _
    (@abelian_snake_third_zeta_iota_after_p1_to_su_path C P t
      Ab A B X D T triple cocone)
    (@eq_trans _ _ _ _
      (@eq_ap
        (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_third_extension_object C P t
            Ab A B X D T triple cocone))
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_third_extension_object C P t
            Ab A B X D T triple cocone))
        (λ h : τ (Hom C
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_third_extension_object C P t
              Ab A B X D T triple cocone)),
          @comp_fapp0 C _ _ _ h
            (@abelian_snake_p1 C P t Ab A B X D triple))
        _ _
        (@abelian_snake_third_su_path C P t
          Ab A B X D T triple cocone))
      (@preadditive_precompose_zero_path C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t
          Ab A B X D T triple cocone)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_third_extension_monomorphism C P t
            Ab A B X D T triple cocone)
          (@comp_fapp0 C _ _ _
            (@cokernel_coannihilator_arrow C
              (@abelian_stability_preadditive C P t Ab)
              (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
              (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_connecting C P t Ab A B X D triple)
              T cocone)
            (@abelian_snake_connecting C P t Ab A B X D triple)))
        (@abelian_snake_p1 C P t Ab A B X D triple)
        (@abelian_snake_third_m_psi_partial_zero_path C P t
          Ab A B X D T triple cocone)));

symbol abelian_snake_third_zeta_iota_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_third_zeta C P t
          Ab A B X D T triple cocone)
        (@abelian_snake_iota C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t
          Ab A B X D T triple cocone)))
≔ @epic_precomposition_zero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_third_extension_object C P t
      Ab A B X D T triple cocone)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_epic C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_third_zeta C P t
        Ab A B X D T triple cocone)
      (@abelian_snake_iota C P t Ab A B X D triple))
    (@abelian_snake_third_zeta_iota_after_p1_zero_path C P t
      Ab A B X D T triple cocone);
