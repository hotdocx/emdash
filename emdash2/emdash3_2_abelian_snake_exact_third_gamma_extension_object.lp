/* Object projection of the canonical gamma-row extension. */

require open emdash.emdash3_2_abelian_snake_exact_third_gamma_extension_foundation;

symbol abelian_snake_third_gamma_extension_object
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
≔ @computational_exact_extension_object C P t
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
      Ab A B X D T triple cocone)
    (@abelian_snake_third_gamma_extension C P t
      Ab A B X D T triple cocone);
