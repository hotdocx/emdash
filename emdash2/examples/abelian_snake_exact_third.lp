/* Reviewer-facing computational exactness at Coker(alpha). */

require open emdash.emdash3_2_abelian_snake_exact_third_result;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_exact_at_coker_alpha C P t Ab A B X D triple
  : τ (@ComputationalExactAt C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_third_exact_pair C P t Ab A B X D triple)
      (@abelian_snake_third_exact_homology C P t Ab A B X D triple));
