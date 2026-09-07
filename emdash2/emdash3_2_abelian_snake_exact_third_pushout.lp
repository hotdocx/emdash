/* Third snake exactness position and the first monic pushout extension. */

require open emdash.emdash3_2_abelian_snake_six_term_inner_cokernel_zero;
require open emdash.emdash3_2_exactness_extensions_to_exact;

symbol abelian_snake_third_exact_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalChainPair C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    (@abelian_snake_cokernel_map_after_connecting_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_third_exact_homology
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalHomologyAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_third_exact_pair C P t Ab A B X D triple))
≔ @computational_homology_at C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_third_exact_pair C P t Ab A B X D triple);

symbol abelian_snake_third_extension_pushout
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
  : τ (@ComputationalPushout C P t
      (@abelian_stability_additive C P t Ab)
      (@abelian_snake_pushout_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      T
      (@abelian_snake_q2 C P t Ab A B X D triple)
      (@cokernel_coannihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple)
        T cocone))
≔ @abelian_selected_pushout C P t Ab
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    T
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cocone);

symbol abelian_snake_third_extension_object
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
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (Obj C)
≔ @computational_pushout_object C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    T
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cocone)
    (@abelian_snake_third_extension_pushout C P t
      Ab A B X D T triple cocone);

symbol abelian_snake_third_extension_monomorphism
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
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (Hom C T
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
≔ @computational_pushout_inj2 C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    T
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cocone)
    (@abelian_snake_third_extension_pushout C P t
      Ab A B X D T triple cocone);

symbol abelian_snake_third_extension_pushout_factor
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
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (Hom C
      (@abelian_snake_pushout_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
≔ @computational_pushout_inj1 C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    T
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cocone)
    (@abelian_snake_third_extension_pushout C P t
      Ab A B X D T triple cocone);

symbol abelian_snake_third_extension_is_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@IsMonic C T
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone)
      (@abelian_snake_third_extension_monomorphism C P t
        Ab A B X D T triple cocone))
≔ @abelian_pushout_monic_injection C P t Ab
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    T
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cocone)
    (@abelian_snake_q2_monic C P t Ab A B X D triple);

symbol abelian_snake_third_extension_path
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
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_third_extension_object C P t
        Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_third_extension_pushout_factor C P t
          Ab A B X D T triple cocone)
        (@abelian_snake_q2 C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_third_extension_monomorphism C P t
          Ab A B X D T triple cocone)
        (@cokernel_coannihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_connecting C P t Ab A B X D triple)
          T cocone)))
≔ @computational_pushout_compatibility_path C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    T
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@cokernel_coannihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cocone)
    (@abelian_snake_third_extension_pushout C P t
      Ab A B X D T triple cocone);
