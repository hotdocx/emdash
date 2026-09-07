/* Dependent whole exact result over the existing six-term snapshot. */

require open emdash.emdash3_2_abelian_snake_six_term_exact_pairs;

// Exactness is indexed by the snapshot actually stored in the result.
symbol AbelianSnakeSixTermExactResult
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : Grpd
≔ `Σ_ snapshot : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple),
    (@AbelianSnakeSixTermExactData C P t Ab A B X D triple snapshot);

// Transparent constructor through the existing dependent Sigma.
symbol abelian_snake_six_term_exact_result_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (snapshot : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  (data : τ (@AbelianSnakeSixTermExactData C P t Ab A B X D triple snapshot))
  : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple)
≔ @Struct_sigma (@AbelianSnakeSixTermResult C P t Ab A B X D triple)
    (λ snapshot : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple),
      (@AbelianSnakeSixTermExactData C P t Ab A B X D triple snapshot))
    snapshot data;

// The underlying snapshot still owns all five arrows and four zero paths.
symbol abelian_snake_six_term_exact_result_snapshot
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple))
  : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple)
≔ sigma_Fst result;

symbol abelian_snake_six_term_exact_result_data
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (result : τ (@AbelianSnakeSixTermExactResult C P t Ab A B X D triple))
  : τ (@AbelianSnakeSixTermExactData C P t Ab A B X D triple
    (@abelian_snake_six_term_exact_result_snapshot C P t Ab A B X D triple result))
≔ sigma_Snd result;
