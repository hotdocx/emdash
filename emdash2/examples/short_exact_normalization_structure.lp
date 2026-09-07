/* Whole normalization retains its actual row and compatible isomorphism points. */

require open emdash.emdash3_2_short_exact_normalization_projections;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (normalized : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab)
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))
    (@computational_cokernel_morphism C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
    (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))))
  (source : τ (@ShortExactNormalizationSourceComparison C P t Ab A B D pair normalized))
  (target : τ (@ShortExactNormalizationTargetComparison C P t Ab A B D pair normalized))
  ⊢ @short_exact_normalization_row C P t Ab A B D pair
    (@short_exact_normalization_intro C P t Ab A B D pair normalized source target)
  ≡ normalized;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (normalized : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab)
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))
    (@computational_cokernel_morphism C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
    (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))))
  (source : τ (@ShortExactNormalizationSourceComparison C P t Ab A B D pair normalized))
  (target : τ (@ShortExactNormalizationTargetComparison C P t Ab A B D pair normalized))
  ⊢ @short_exact_normalization_source_point C P t Ab A B D pair
    (@short_exact_normalization_intro C P t Ab A B D pair normalized source target)
  ≡ source;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (normalized : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab)
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))
    (@computational_cokernel_morphism C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
    (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))))
  (source : τ (@ShortExactNormalizationSourceComparison C P t Ab A B D pair normalized))
  (target : τ (@ShortExactNormalizationTargetComparison C P t Ab A B D pair normalized))
  ⊢ @short_exact_normalization_target_point C P t Ab A B D pair
    (@short_exact_normalization_intro C P t Ab A B D pair normalized source target)
  ≡ target;

// Compatibility for one row cannot be silently attached to another.
assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (normalized other : τ (@ComputationalShortExactRow C P t
    (@computational_abelian_preabelian C P t Ab) (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))
    (@computational_cokernel_morphism C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
    (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair)))))
  (source : τ (@ShortExactNormalizationSourceComparison C P t Ab A B D pair normalized))
  (target : τ (@ShortExactNormalizationTargetComparison C P t Ab A B D pair other))
  ⊢ @short_exact_normalization_intro C P t Ab A B D pair other source target
  : τ (@ShortExactNormalization C P t Ab A B D pair);
