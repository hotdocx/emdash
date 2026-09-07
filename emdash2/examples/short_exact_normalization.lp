/* Canonical whole normalization recovers the chosen row and universal comparison data. */

require open emdash.emdash3_2_short_exact_normalization;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ (@short_exact_normalization_row C P t Ab A B D pair
    (@short_exact_normalization C P t Ab A B D pair short))
  ≡ (@selected_short_exact_row C P t (@computational_abelian_preabelian C P t Ab) A B
    (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ (@short_exact_normalization_left_iso C P t Ab A B D pair
    (@short_exact_normalization C P t Ab A B D pair short))
  ≡ (@short_exact_normalization_source_iso C P t Ab A B D pair short);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ (@short_exact_normalization_right_iso C P t Ab A B D pair
    (@short_exact_normalization C P t Ab A B D pair short))
  ≡ (@short_exact_normalization_target_iso C P t Ab A B D pair short);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ (@short_exact_normalization_left_path C P t Ab A B D pair
    (@short_exact_normalization C P t Ab A B D pair short))
  ≡ (sigma_Snd (@short_exact_normalization_source_factor C P t Ab A B D pair short));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ (@short_exact_normalization_right_path C P t Ab A B D pair
    (@short_exact_normalization C P t Ab A B D pair short))
  ≡ (sigma_Snd (@short_exact_normalization_target_factor C P t Ab A B D pair short));
