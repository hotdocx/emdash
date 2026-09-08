/* Postcompose the original second-map reconstruction at its exact owner. */
require open emdash.emdash3_2_abelian_snake_six_term_kernel_beta_foundation;
require open emdash.emdash3_2_hom_factor_composition;

symbol abelian_snake_second_postcomp_path
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C (@abelian_stability_preadditive C P t Ab) A B X D))
  [T : τ (Obj C)]
  (e : τ (Hom C (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T))
  : τ (@= (Hom C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) T)
      (@comp_fapp0 C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) T (@comp_fapp0 C (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@computational_kernel_morphism C (@abelian_stability_preadditive C P t Ab) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D (@abelian_snake_gamma C P t Ab A B X D triple) (@abelian_snake_gamma_kernel C P t Ab A B X D triple))) (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
      (@comp_fapp0 C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B T (@comp_fapp0 C B (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@abelian_snake_epsilon C P t Ab A B X D triple)) (@abelian_snake_k_beta C P t Ab A B X D triple)))
≔ @hom_factor_paste_path C (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) T
    (@abelian_snake_k_beta C P t Ab A B X D triple) (@computational_kernel_morphism C (@abelian_stability_preadditive C P t Ab) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D (@abelian_snake_gamma C P t Ab A B X D triple) (@abelian_snake_gamma_kernel C P t Ab A B X D triple)) (@comp_fapp0 C (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@computational_kernel_morphism C (@abelian_stability_preadditive C P t Ab) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D (@abelian_snake_gamma C P t Ab A B X D triple) (@abelian_snake_gamma_kernel C P t Ab A B X D triple))) (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple) (@id C (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)) (@abelian_snake_epsilon C P t Ab A B X D triple) e
    (@abelian_snake_ker_beta_to_ker_gamma_path C P t Ab A B X D triple)
    (@eq_refl (Hom C (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) T) (@comp_fapp0 C (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) T e (@computational_kernel_morphism C (@abelian_stability_preadditive C P t Ab) (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D (@abelian_snake_gamma C P t Ab A B X D triple) (@abelian_snake_gamma_kernel C P t Ab A B X D triple))));
