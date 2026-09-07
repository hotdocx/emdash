/* The canonical snake snapshot carries the four already-proved exactness witnesses. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_data_intro;
require open emdash.emdash3_2_abelian_snake_six_term_exact_result_projections;
require open emdash.emdash3_2_abelian_snake_six_term_canonical_exactness;

symbol abelian_snake_six_term_exact_data
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@AbelianSnakeSixTermExactData C P t Ab A B X D triple
      (@abelian_snake_six_term_result C P t Ab A B X D triple))
≔ @abelian_snake_six_term_exact_data_intro C P t Ab A B X D triple
    (@abelian_snake_six_term_result C P t Ab A B X D triple)
    (@abelian_snake_six_term_canonical_first_exactness C P t Ab A B X D triple)
    (@abelian_snake_six_term_canonical_second_exactness C P t Ab A B X D triple)
    (@abelian_snake_six_term_canonical_third_exactness C P t Ab A B X D triple)
    (@abelian_snake_six_term_canonical_fourth_exactness C P t Ab A B X D triple);

// One dependent whole result; its snapshot owns all maps and adjacent zeros.
symbol abelian_snake_six_term_exact_result
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple)
≔ @abelian_snake_six_term_exact_result_intro C P t Ab A B X D triple
    (@abelian_snake_six_term_result C P t Ab A B X D triple)
    (@abelian_snake_six_term_exact_data C P t Ab A B X D triple);
