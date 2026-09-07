/* Canonical pair identities, each witnessed by reflexivity after projection. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_pairs;
require open emdash.emdash3_2_abelian_snake_exact_first_foundation;
require open emdash.emdash3_2_abelian_snake_exact_second_pullback;
require open emdash.emdash3_2_abelian_snake_exact_third_pushout;
require open emdash.emdash3_2_abelian_snake_exact_fourth_foundation;

symbol abelian_snake_six_term_first_pair_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@abelian_snake_six_term_first_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple))
      (@abelian_snake_first_exact_pair C P t Ab A B X D triple))
≔ @eq_refl (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
    (@abelian_snake_first_exact_pair C P t Ab A B X D triple);

symbol abelian_snake_six_term_second_pair_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
      (@abelian_snake_six_term_second_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple))
      (@abelian_snake_second_exact_pair C P t Ab A B X D triple))
≔ @eq_refl (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
    (@abelian_snake_second_exact_pair C P t Ab A B X D triple);

symbol abelian_snake_six_term_third_pair_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@abelian_snake_six_term_third_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple))
      (@abelian_snake_third_exact_pair C P t Ab A B X D triple))
≔ @eq_refl (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
    (@abelian_snake_third_exact_pair C P t Ab A B X D triple);

symbol abelian_snake_six_term_fourth_pair_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple
        (@abelian_snake_six_term_result C P t Ab A B X D triple))
      (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple))
≔ @eq_refl (@ComputationalChainPair C (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
    (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple);
