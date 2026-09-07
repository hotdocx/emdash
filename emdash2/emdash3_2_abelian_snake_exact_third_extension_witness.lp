/* Compose the two selected monomorphic extensions. */

require open emdash.emdash3_2_abelian_snake_exact_third_extension_comparison;

symbol abelian_snake_third_total_extension_monomorphism
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
  : τ (Hom C T (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
≔ (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple
  cocone) (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone));

symbol abelian_snake_third_total_extension_is_monic
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
  : τ (@IsMonic C T (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_total_extension_monomorphism C P t Ab A B X D T triple cocone))
≔ @is_monic_comp C T (@abelian_snake_third_extension_object C P t Ab A B X D T triple cocone)
  (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone)
      (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_extension_is_monic C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_gamma_extension_is_monic C P t Ab A B X D T triple cocone);

symbol abelian_snake_third_exact_extension
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
  : τ (@ComputationalExactExtensionWitness C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C
        P t Ab A B X D triple) (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_third_exact_pair C P t Ab A B X D triple) T cocone)
≔ @computational_exact_extension_intro C P t (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_third_exact_pair C P t Ab A B X D triple) T cocone
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
      (@abelian_snake_third_total_extension_monomorphism C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_total_extension_is_monic C P t Ab A B X D T triple cocone)
    (@abelian_snake_third_cokernel_factor C P t Ab A B X D T triple cocone)
      (@abelian_snake_third_extension_comparison_path C P t Ab A B X D T triple cocone);
