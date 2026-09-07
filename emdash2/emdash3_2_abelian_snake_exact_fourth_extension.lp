/* Canonical extension of psi c_beta through lambda. */

require open emdash.emdash3_2_abelian_snake_exact_fourth_foundation;

symbol abelian_snake_fourth_lambda_extension
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (@ComputationalExactExtensionWitness C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X D
      (@abelian_canonical_kernel_pair_explicit C P t
        (@abelian_stability_preabelian C P t Ab) X D
        (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
      T
      (@abelian_snake_fourth_lambda_cocone C P t Ab A B X D T triple cocone))
≔
  (@abelian_canonical_kernel_extensions C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab) X D
    (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
  T
  (@abelian_snake_fourth_lambda_cocone C P t Ab A B X D T triple cocone);
