/* Reindex exactness along an equality of chain-pair data. */

require open emdash.emdash3_2_short_exact_sequences;

// The selected kernel/homology owner is reused on both ends of the same pair family.
symbol computational_exactness_reindex
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (p q : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t PA) A B D))
  (path : τ (@= (@ComputationalChainPair C
    (@computational_homology_preadditive C P t PA) A B D) p q))
  (exact : τ (@computational_exact_at_selected C P t PA A B D q))
  : τ (@computational_exact_at_selected C P t PA A B D p)
≔ @ind_eq
    (@ComputationalChainPair C
      (@computational_homology_preadditive C P t PA) A B D)
    p q path
    (λ r : τ (@ComputationalChainPair C
        (@computational_homology_preadditive C P t PA) A B D),
      @computational_exact_at_selected C P t PA A B D r)
    exact;
