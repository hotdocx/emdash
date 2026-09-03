/* Reviewer-facing cokernel-side maps of the six-term snake sequence. */

require open emdash.emdash3_2_abelian_snake_six_term_cokernels;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple
  : τ (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_coker_alpha_to_coker_beta_path C P t
      Ab A B X D triple
  : τ (@= (Hom C
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_beta C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple
  : τ (Hom C
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_coker_beta_to_coker_gamma_path C P t
      Ab A B X D triple
  : τ (@= (Hom C X
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple)
        (@abelian_snake_c_beta C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_gamma C P t Ab A B X D triple)
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)));
