/* Reviewer-facing outer zero composites of the six-term snake sequence. */

require open emdash.emdash3_2_abelian_snake_six_term_kernel_zero;
require open emdash.emdash3_2_abelian_snake_six_term_cokernel_zero;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_kernel_maps_zero_path C P t Ab A B X D triple
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
        (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_cokernel_maps_zero_path C P t Ab A B X D triple
  : τ (@= (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)));
