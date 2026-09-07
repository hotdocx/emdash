/* Each actual snapshot pair retains both arrows and its zero witness. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_pairs;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_dnext C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_first_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_d C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_second_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_path C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_first_zero_path C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_dnext C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_second_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_d C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_connecting_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_path C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_second_zero_path C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_dnext C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_connecting_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_d C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_fourth_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_path C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_third_zero_path C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_dnext C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_fourth_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_d C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_fifth_arrow C P t Ab A B X D triple result);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_path C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_six_term_fourth_zero_path C P t Ab A B X D triple result);

// Conversion guard: an arbitrary stored map must not become the canonical map.
assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  ⊢ @computational_chain_pair_dnext C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple result)
  ≡ (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple);
