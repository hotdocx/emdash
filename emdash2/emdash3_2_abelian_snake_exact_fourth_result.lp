/* Extension family and exactness at Coker(beta). */

require open emdash.emdash3_2_abelian_snake_exact_fourth_comparison;

symbol abelian_snake_fourth_exact_extension
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
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple) T cocone)
≔ @computational_exact_extension_intro C P t
  (@abelian_stability_preabelian C P t Ab)
  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
  (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
  (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
  (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple) T cocone
  (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_extension_is_monic C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_cokernel_factor C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_extension_comparison_path C P t Ab A B X D T triple cocone);

symbol abelian_snake_fourth_exact_extensions
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ
    (@HasComputationalExactExtensions C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple))
≔ λ T : τ (Obj C),
   λ cocone : τ
  (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T),
  (@abelian_snake_fourth_exact_extension C P t Ab A B X D T triple cocone);

symbol abelian_snake_exact_at_coker_beta
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ
    (@ComputationalExactAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple)
      (@abelian_snake_fourth_exact_homology C P t Ab A B X D triple))
≔ @computational_exact_at_from_extensions C P t Ab
  (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
  (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
  (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
  (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple)
  (@abelian_snake_fourth_exact_homology C P t Ab A B X D triple)
  (@abelian_snake_fourth_exact_extensions C P t Ab A B X D triple);
