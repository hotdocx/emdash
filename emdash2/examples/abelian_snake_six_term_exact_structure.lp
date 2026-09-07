/* Generic whole-result beta checks and the snapshot-dependency guard. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_result_projections;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (snapshot : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  (data : τ (@AbelianSnakeSixTermExactData C P t Ab A B X D triple snapshot))
  ⊢ (@abelian_snake_six_term_exact_result_snapshot C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result_intro C P t Ab A B X D triple snapshot data))
  ≡ snapshot;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (snapshot : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  (data : τ (@AbelianSnakeSixTermExactData C P t Ab A B X D triple snapshot))
  ⊢ (@abelian_snake_six_term_exact_result_data C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result_intro C P t Ab A B X D triple snapshot data))
  ≡ data;

// Evidence for one arbitrary snapshot cannot be attached to another.
assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (snapshot other : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  (data : τ (@AbelianSnakeSixTermExactData C P t Ab A B X D triple snapshot))
  ⊢ @abelian_snake_six_term_exact_result_intro C P t
      Ab A B X D triple other data
  : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple);
