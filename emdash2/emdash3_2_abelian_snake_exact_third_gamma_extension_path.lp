/* Selected gamma-row extension: path projection. */

require open emdash.emdash3_2_abelian_snake_exact_third_gamma_extension_factor;

symbol abelian_snake_third_gamma_extension_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple) T))
  : τ (@= (Hom C (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T
        triple cocone)
        (@abelian_snake_third_zeta C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_factor C P t Ab A B X D T triple
        cocone)
        (@abelian_snake_gamma C P t Ab A B X D triple)))
≔ @computational_exact_extension_path C P t (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    D
    (@abelian_canonical_kernel_pair_explicit C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D (@abelian_snake_gamma C P t Ab A
        B X D triple))
    (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_gamma_cocone C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_gamma_extension C P t Ab A B X D T triple cocone);
