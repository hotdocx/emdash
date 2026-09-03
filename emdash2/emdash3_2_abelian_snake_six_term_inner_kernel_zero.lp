/* Second adjacent-zero point after cancellation through monic q2. */

require open emdash.emdash3_2_abelian_snake_six_term_inner_kernel_q2_zero_foundation;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_connecting_after_kernel_map_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_connecting C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)))
≔ @monic_postcomposition_zero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_pushout_object C P t Ab A B X D triple)
    (@abelian_snake_q2 C P t Ab A B X D triple)
    (@abelian_snake_q2_monic C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_connecting C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
    (@abelian_snake_q2_after_connecting_kernel_map_zero_path C P t
      Ab A B X D triple);
