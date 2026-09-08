/* Reviewer-facing covered snake reconstruction and its factor point. */

require open emdash.emdash3_2_abelian_snake_covered_reconstruction;
require open emdash.emdash3_2_hom_factor_spaces;

// The cover law makes the original lambda lift an actual pi-factor point.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @hom_postcomp_factor_intro C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_pi C P t Ab A B X D triple)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_connecting C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@abelian_snake_beta_p2_lambda_lift C P t Ab A B X D triple)
      (@eq_sym _ _ _
        (@abelian_snake_connecting_after_p1_path C P t Ab A B X D triple))
  : τ (@HomPostcompFactor C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_pi C P t Ab A B X D triple)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_connecting C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple)));

// Reconstruction does not identify the covered connecting arrow with zero.
assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_connecting_after_p1_path C P t Ab A B X D triple
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_connecting C P t Ab A B X D triple)
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)));
