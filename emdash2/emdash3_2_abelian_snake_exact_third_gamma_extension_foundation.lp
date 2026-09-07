/* Canonical kernel-row extension of zeta through gamma. */

require open emdash.emdash3_2_abelian_snake_exact_third_zeta_zero;
require open emdash.emdash3_2_abelian_canonical_kernel_extensions;

symbol abelian_snake_third_gamma_cocone
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
  : τ (@CokernelCoannihilator C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_iota C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
    (λ h : τ (Hom C
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t
          Ab A B X D T triple cocone)),
      @= (Hom C
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_third_extension_object C P t
          Ab A B X D T triple cocone))
        (@comp_fapp0 C _ _ _ h
          (@abelian_snake_iota C P t Ab A B X D triple))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_third_extension_object C P t
            Ab A B X D T triple cocone)))
    (@abelian_snake_third_zeta C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_zeta_iota_zero_path C P t
      Ab A B X D T triple cocone);

symbol abelian_snake_third_gamma_extension
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
  : τ (@ComputationalExactExtensionWitness C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      D
      (@abelian_canonical_kernel_pair_explicit C P t
        (@abelian_stability_preabelian C P t Ab)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
        D
        (@abelian_snake_gamma C P t Ab A B X D triple))
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone)
      (@abelian_snake_third_gamma_cocone C P t
        Ab A B X D T triple cocone))
≔ (@abelian_canonical_kernel_extensions C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    D
    (@abelian_snake_gamma C P t Ab A B X D triple))
    (@abelian_snake_third_extension_object C P t
      Ab A B X D T triple cocone)
    (@abelian_snake_third_gamma_cocone C P t
      Ab A B X D T triple cocone);
