/* Exactness reindexing computes to the original proof on reflexivity. */

require open emdash.emdash3_2_exactness_reindex;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t PA) A B D))
  (exact : τ (@computational_exact_at_selected C P t PA A B D pair))
  ⊢ @computational_exactness_reindex C P t PA A B D
      pair pair
      (@eq_refl (@ComputationalChainPair C
        (@computational_homology_preadditive C P t PA) A B D) pair)
      exact
  ≡ exact;
