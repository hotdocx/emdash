/* Reuse exactness at the pair owner before opening its large predicate. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_pair_paths;
require open emdash.emdash3_2_exactness_reindex;
require open emdash.emdash3_2_abelian_snake_exact_first_result;
require open emdash.emdash3_2_abelian_snake_exact_second_result;
require open emdash.emdash3_2_abelian_snake_exact_third_result;
require open emdash.emdash3_2_abelian_snake_exact_fourth_result;

// The reflexivity path makes this adapter compute to the existing proof.
symbol abelian_snake_six_term_canonical_first_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple)))
≔ @computational_exactness_reindex C P t (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_first_pair C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple))
    (@abelian_snake_first_exact_pair C P t Ab A B X D triple)
    (@abelian_snake_six_term_first_pair_path C P t Ab A B X D triple)
    (@abelian_snake_exact_at_ker_beta C P t Ab A B X D triple);

// The reflexivity path makes this adapter compute to the existing proof.
symbol abelian_snake_six_term_canonical_second_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple)))
≔ @computational_exactness_reindex C P t (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_second_pair C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple))
    (@abelian_snake_second_exact_pair C P t Ab A B X D triple)
    (@abelian_snake_six_term_second_pair_path C P t Ab A B X D triple)
    (@abelian_snake_exact_at_ker_gamma C P t Ab A B X D triple);

// The reflexivity path makes this adapter compute to the existing proof.
symbol abelian_snake_six_term_canonical_third_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple)))
≔ @computational_exactness_reindex C P t (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_third_pair C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple))
    (@abelian_snake_third_exact_pair C P t Ab A B X D triple)
    (@abelian_snake_six_term_third_pair_path C P t Ab A B X D triple)
    (@abelian_snake_exact_at_coker_alpha C P t Ab A B X D triple);

// The reflexivity path makes this adapter compute to the existing proof.
symbol abelian_snake_six_term_canonical_fourth_exactness
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@computational_exact_at_selected C P t (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple)))
≔ @computational_exactness_reindex C P t (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple))
    (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple)
    (@abelian_snake_six_term_fourth_pair_path C P t Ab A B X D triple)
    (@abelian_snake_exact_at_coker_beta C P t Ab A B X D triple);
