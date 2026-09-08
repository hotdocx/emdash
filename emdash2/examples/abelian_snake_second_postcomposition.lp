/* Independent typed consumer at the original supplied choices. */
require open emdash.emdash3_2_abelian_snake_second_postcomposition;

// Reconstruction is a derived path, not a new runtime equality.
assertnot
  (C : Cat) (P : τ (Functor (Product_cat C C) C)) (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C (@abelian_stability_preadditive C P t Ab) A B X D))
  (T : τ (Obj C))
  (e : τ (Hom C (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T))
  ⊢ @eq_refl (Hom C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) T) (@comp_fapp0 C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B T (@comp_fapp0 C B (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@abelian_snake_epsilon C P t Ab A B X D triple)) (@abelian_snake_k_beta C P t Ab A B X D triple)) : τ (@= (Hom C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) T)
      (@comp_fapp0 C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) T (@comp_fapp0 C (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@computational_kernel_morphism C (@abelian_stability_preadditive C P t Ab) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D (@abelian_snake_gamma C P t Ab A B X D triple) (@abelian_snake_gamma_kernel C P t Ab A B X D triple))) (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
      (@comp_fapp0 C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B T (@comp_fapp0 C B (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@abelian_snake_epsilon C P t Ab A B X D triple)) (@abelian_snake_k_beta C P t Ab A B X D triple)));

assert
  (C : Cat) (P : τ (Functor (Product_cat C C) C)) (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C (@abelian_stability_preadditive C P t Ab) A B X D))
  (T : τ (Obj C))
  (e : τ (Hom C (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T))
  ⊢ @abelian_snake_second_postcomp_path C P t Ab A B X D triple T e : τ (@= (Hom C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) T)
      (@comp_fapp0 C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) T (@comp_fapp0 C (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@computational_kernel_morphism C (@abelian_stability_preadditive C P t Ab) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D (@abelian_snake_gamma C P t Ab A B X D triple) (@abelian_snake_gamma_kernel C P t Ab A B X D triple))) (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
      (@comp_fapp0 C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B T (@comp_fapp0 C B (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@abelian_snake_epsilon C P t Ab A B X D triple)) (@abelian_snake_k_beta C P t Ab A B X D triple)));
