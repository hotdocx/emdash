/* First adjacent-zero point after monic kernel cancellation. */

require open emdash.emdash3_2_abelian_snake_six_term_kernel_zero_foundation;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_kernel_maps_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_gamma_kernel C P t Ab A B X D triple)))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
        (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple) D
          (@abelian_snake_gamma C P t Ab A B X D triple)
          (@abelian_snake_gamma_kernel C P t Ab A B X D triple))))
≔ @computational_kernel_postzero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_kernel C P t Ab A B X D triple)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
      (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple))
    (@abelian_snake_iota_after_kernel_composite_zero_path C P t
      Ab A B X D triple);
