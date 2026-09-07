/* Usability constructor for the four snapshot-indexed exactness witnesses. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_pairs;

symbol abelian_snake_six_term_exact_data_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (snapshot : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  (e0 : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple snapshot)))
  (e1 : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple snapshot)))
  (e2 : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple snapshot)))
  (e3 : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple snapshot)))
  : τ (@AbelianSnakeSixTermExactData C P t Ab A B X D triple snapshot)
≔ @Product_pair_grpd _ _ e0
    (@Product_pair_grpd _ _ e1
      (@Product_pair_grpd _ _ e2 e3));
