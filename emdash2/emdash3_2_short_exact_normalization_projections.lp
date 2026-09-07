/* Whole normalization projections retain the actual comparison fibres. */

require open emdash.emdash3_2_short_exact_normalization_foundation;

symbol short_exact_normalization_intro
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
  (source : τ (@ShortExactNormalizationSourceComparison C P t Ab A B D pair normalized))
  (target : τ (@ShortExactNormalizationTargetComparison C P t Ab A B D pair normalized))
  : τ (@ShortExactNormalization C P t Ab A B D pair)
≔ @Struct_sigma (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab)
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
  (@computational_abelian_preabelian C P t Ab))) A B D pair))))
    (λ normalized : τ (@ComputationalShortExactRow C P t
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
      (@computational_abelian_preabelian C P t Ab))) A B D pair)))),
      @Product_grpd
        (@ShortExactNormalizationSourceComparison C P t Ab A B D pair normalized)
        (@ShortExactNormalizationTargetComparison C P t Ab A B D pair normalized))
    normalized (@Product_pair_grpd _ _ source target);

symbol short_exact_normalization_source_point
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (result : τ (@ShortExactNormalization C P t Ab A B D pair))
  : τ (@ShortExactNormalizationSourceComparison C P t Ab A B D pair
    (@short_exact_normalization_row C P t Ab A B D pair result))
≔ sigma_Fst (sigma_Snd result);

symbol short_exact_normalization_target_point
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (result : τ (@ShortExactNormalization C P t Ab A B D pair))
  : τ (@ShortExactNormalizationTargetComparison C P t Ab A B D pair
    (@short_exact_normalization_row C P t Ab A B D pair result))
≔ sigma_Snd (sigma_Snd result);

symbol short_exact_normalization_left_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (result : τ (@ShortExactNormalization C P t Ab A B D pair))
  : τ (@IsoEvidence C A (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) B
    (@computational_cokernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
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
    (@computational_abelian_preabelian C P t Ab))) A B D pair))))
≔ sigma_Fst (@short_exact_normalization_source_point C P t Ab A B D pair result);

symbol short_exact_normalization_right_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (result : τ (@ShortExactNormalization C P t Ab A B D pair))
  : τ (@IsoEvidence C (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
    (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
    (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
    (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D pair))) D)
≔ sigma_Fst (@short_exact_normalization_target_point C P t Ab A B D pair result);

symbol short_exact_normalization_left_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (result : τ (@ShortExactNormalization C P t Ab A B D pair))
  : τ (@= (Hom C A B)
      (@comp_fapp0 C _ _ _ (@computational_chain_pair_dnext C (@additive_preadditive C P t
        (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab)))
        (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@computational_cokernel_morphism C (@additive_preadditive C P t
        (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
        (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
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
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
        (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@computational_cokernel_morphism C (@additive_preadditive C P t
        (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
        (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
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
        (@computational_abelian_preabelian C P t Ab))) A B D pair)))
        (@short_exact_normalization_row C P t Ab A B D pair result)))
        (@iso_evidence_to C A (@computational_kernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) B
          (@computational_cokernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)
          (@preabelian_cokernel C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@computational_cokernel_morphism C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)
          (@preabelian_cokernel C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@computational_image C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@short_exact_normalization_left_iso C P t Ab A B D pair result)))
      (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))
≔ sigma_Snd (@short_exact_normalization_source_point C P t Ab A B D pair result);

symbol short_exact_normalization_right_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t
    (@computational_abelian_preabelian C P t Ab))) A B D))
  (result : τ (@ShortExactNormalization C P t Ab A B D pair))
  : τ (@= (Hom C B D)
      (@comp_fapp0 C _ _ _ (@iso_evidence_to C (@computational_cokernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
        (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
        (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))) D
        (@short_exact_normalization_right_iso C P t Ab A B D pair result))
        (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) (@computational_kernel_object C
          (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
          (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
          (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
          (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
          (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@computational_cokernel_morphism C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)
          (@preabelian_cokernel C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@computational_image C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
          (@computational_cokernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)
          (@preabelian_cokernel C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
          (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) B (@computational_cokernel_object C
          (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B (@computational_chain_pair_dnext C
          (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B D pair) (@preabelian_cokernel C P t
          (@computational_abelian_preabelian C P t Ab) A B (@computational_chain_pair_dnext C
          (@additive_preadditive C P t (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@computational_cokernel_morphism C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)
          (@preabelian_cokernel C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@computational_image C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t Ab))) A B D pair))) B
          (@computational_cokernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)
          (@preabelian_cokernel C P t (@computational_abelian_preabelian C P t Ab) A B
          (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t (@computational_abelian_preabelian C P t Ab))) A B D pair)))
          (@short_exact_normalization_row C P t Ab A B D pair result))))
      (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t
        (@computational_abelian_preabelian C P t Ab))) A B D pair))
≔ sigma_Snd (@short_exact_normalization_target_point C P t Ab A B D pair result);
