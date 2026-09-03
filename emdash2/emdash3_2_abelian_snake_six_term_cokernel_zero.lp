/* Fourth adjacent-zero point after epic cokernel cancellation. */

require open emdash.emdash3_2_abelian_snake_six_term_cokernel_zero_foundation;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_cokernel_maps_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@computational_cokernel_object C
        (@abelian_stability_preadditive C P t Ab) A
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_alpha C P t Ab A B X D triple)
        (@abelian_snake_alpha_cokernel C P t Ab A B X D triple))
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@computational_cokernel_object C
          (@abelian_stability_preadditive C P t Ab) A
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_alpha C P t Ab A B X D triple)
          (@abelian_snake_alpha_cokernel C P t Ab A B X D triple))
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))
≔ @computational_cokernel_prezero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_cokernel C P t Ab A B X D triple)
    (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple))
    (@abelian_snake_cokernel_composite_after_pi_zero_path C P t
      Ab A B X D triple);
