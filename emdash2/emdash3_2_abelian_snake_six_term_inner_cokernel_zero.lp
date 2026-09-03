/* Third adjacent-zero point after cancellation through epic p1. */

require open emdash.emdash3_2_abelian_snake_six_term_inner_cokernel_p1_zero_foundation;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_cokernel_map_after_connecting_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_alpha_to_coker_beta C P t
          Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ @epic_precomposition_zero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_epic C P t Ab A B X D triple)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_coker_alpha_to_coker_beta C P t
        Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple))
    (@abelian_snake_cokernel_composite_after_p1_zero_path C P t
      Ab A B X D triple);
