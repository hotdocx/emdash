/* Normalization uses generic comparison fibres on the actual stored row. */

require open emdash.emdash3_2_short_exact_row_comparison_fibres;
require open emdash.emdash3_2_selected_short_exact_rows;
require open emdash.emdash3_2_short_exact_cokernel_comparison;
require open emdash.emdash3_2_monic_image_comparison;

symbol ShortExactNormalizationSourceComparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
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
  : Grpd
≔ @ShortExactRowSourceComparison C P t (@computational_abelian_preabelian C P t Ab) A
  (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_cokernel_morphism C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) normalized;

symbol ShortExactNormalizationTargetComparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
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
  : Grpd
≔ @ShortExactRowTargetComparison C P t (@computational_abelian_preabelian C P t Ab)
  (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_cokernel_morphism C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) D (@computational_chain_pair_d C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) normalized;

symbol ShortExactNormalization
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  : Grpd
≔ `Σ_ normalized : τ (@ComputationalShortExactRow C P t
  (@computational_abelian_preabelian C P t Ab) (@computational_kernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_cokernel_morphism C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) (@computational_image C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair))) B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
  (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
  (@additive_preadditive C P t (@preabelian_additive C P t
  (@computational_abelian_preabelian C P t Ab))) A B D pair)))),
    @Product_grpd
      (@ShortExactNormalizationSourceComparison C P t Ab A B D pair normalized)
      (@ShortExactNormalizationTargetComparison C P t Ab A B D pair normalized);

symbol short_exact_normalization_row
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (result : τ (@ShortExactNormalization C P t Ab A B D pair))
  : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab)
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
    (@computational_abelian_preabelian C P t Ab))) A B D pair))))
≔ sigma_Fst result;
