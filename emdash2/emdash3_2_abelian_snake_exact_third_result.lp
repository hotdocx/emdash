/* Monomorphic extension family and exactness at Coker(alpha). */

require open emdash.emdash3_2_abelian_snake_exact_third_extension_witness;

symbol abelian_snake_third_exact_extensions
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@HasComputationalExactExtensions C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C
        P t Ab A B X D triple) (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_third_exact_pair C P t Ab A B X D triple))
≔ λ T : τ (Obj C),
   λ cocone : τ (@CokernelCoannihilator C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C
        P t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T),
     (@abelian_snake_third_exact_extension C P t Ab A B X D T triple cocone);

symbol abelian_snake_exact_at_coker_alpha
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalExactAt C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C
        P t Ab A B X D triple) (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_third_exact_pair C P t Ab A B X D triple)
      (@abelian_snake_third_exact_homology C P t Ab A B X D triple))
≔ @computational_exact_at_from_extensions C P t Ab
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_third_exact_pair C P t Ab A B X D triple)
    (@abelian_snake_third_exact_homology C P t Ab A B X D triple)
    (@abelian_snake_third_exact_extensions C P t Ab A B X D triple);
