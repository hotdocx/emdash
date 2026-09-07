/* Canonical exact result reduces to the existing snapshot and four canonical exactness instances.
  */

require open emdash.emdash3_2_abelian_snake_six_term_exact_result;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_first_pair C P t Ab A B X D triple
    (@abelian_snake_six_term_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_first_exact_pair C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_second_pair C P t Ab A B X D triple
    (@abelian_snake_six_term_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_second_exact_pair C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_third_pair C P t Ab A B X D triple
    (@abelian_snake_six_term_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_third_exact_pair C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_fourth_pair C P t Ab A B X D triple
    (@abelian_snake_six_term_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_fourth_exact_pair C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_exact_result_snapshot C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_six_term_result C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_exact_result_data C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_six_term_exact_data C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_first_exactness C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_six_term_canonical_first_exactness C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_second_exactness C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_six_term_canonical_second_exactness C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_third_exactness C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_six_term_canonical_third_exactness C P t Ab A B X D triple);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ (@abelian_snake_six_term_fourth_exactness C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result C P t Ab A B X D triple))
  ≡ (@abelian_snake_six_term_canonical_fourth_exactness C P t Ab A B X D triple);
