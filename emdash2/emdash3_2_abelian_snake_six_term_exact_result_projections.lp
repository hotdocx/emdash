/* Exactness projections retain their dependence on the stored snapshot. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_result_foundation;

symbol abelian_snake_six_term_first_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_exact_result_snapshot C P t Ab A B X D triple result)))
≔ sigma_Fst (@abelian_snake_six_term_exact_result_data C P t Ab A B X D triple result);

symbol abelian_snake_six_term_second_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_exact_result_snapshot C P t Ab A B X D triple result)))
≔ sigma_Fst (sigma_Snd (@abelian_snake_six_term_exact_result_data C P t Ab A B X D triple result));

symbol abelian_snake_six_term_third_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_exact_result_snapshot C P t Ab A B X D triple result)))
≔ sigma_Fst (sigma_Snd (sigma_Snd
  (@abelian_snake_six_term_exact_result_data C P t Ab A B X D triple result)));

symbol abelian_snake_six_term_fourth_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_exact_result_snapshot C P t Ab A B X D triple result)))
≔ sigma_Snd (sigma_Snd (sigma_Snd
  (@abelian_snake_six_term_exact_result_data C P t Ab A B X D triple result)));
