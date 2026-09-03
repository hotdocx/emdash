/* Reviewer-facing whole six-term snake snapshot and its projections. */

require open emdash.emdash3_2_abelian_snake_six_term_result_projections;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_first_arrow C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_second_arrow C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_connecting_arrow C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_connecting C P t Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_fourth_arrow C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_fifth_arrow C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_coker_beta_to_coker_gamma C P t Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_first_zero_path C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_kernel_maps_zero_path C P t Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_second_zero_path C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_connecting_after_kernel_map_zero_path C P t
      Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_third_zero_path C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_cokernel_map_after_connecting_zero_path C P t
      Ab A B X D triple;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_six_term_fourth_zero_path C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple)
  ≡ @abelian_snake_cokernel_maps_zero_path C P t Ab A B X D triple;
