/* Reviewer-facing kernel-side maps of the six-term snake sequence. */

require open emdash.emdash3_2_abelian_snake_six_term_kernels;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple
  : τ (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_ker_alpha_to_ker_beta_path C P t Ab A B X D triple
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple) B)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_k_beta C P t Ab A B X D triple)
        (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_k_alpha C P t Ab A B X D triple)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple
  : τ (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_ker_beta_to_ker_gamma_path C P t Ab A B X D triple
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_k_beta C P t Ab A B X D triple)));
