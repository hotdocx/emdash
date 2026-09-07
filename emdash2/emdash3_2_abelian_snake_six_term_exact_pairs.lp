/* Adjacent chain pairs and exactness data of the actual stored snapshot. */

require open emdash.emdash3_2_abelian_snake_six_term_result_projections;
require open emdash.emdash3_2_short_exact_sequences;

// The first adjacent pair uses the stored arrows and their stored zero.
symbol abelian_snake_six_term_first_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_first_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_second_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_first_zero_path C P t Ab A B X D triple result);

// The second adjacent pair uses the stored arrows and their stored zero.
symbol abelian_snake_six_term_second_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_second_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_connecting_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_second_zero_path C P t Ab A B X D triple result);

// The third adjacent pair uses the stored arrows and their stored zero.
symbol abelian_snake_six_term_third_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_connecting_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_fourth_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_third_zero_path C P t Ab A B X D triple result);

// The fourth adjacent pair uses the stored arrows and their stored zero.
symbol abelian_snake_six_term_fourth_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_fourth_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_fifth_arrow C P t Ab A B X D triple result)
    (@abelian_snake_six_term_fourth_zero_path C P t Ab A B X D triple result);

// Four exactness witnesses, each for the selected homology of its actual pair.
symbol AbelianSnakeSixTermExactData
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : Grpd
≔ @Product_grpd
    (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple result))
    (@Product_grpd
      (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple result))
      (@Product_grpd
        (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple result))
        (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple result))));
