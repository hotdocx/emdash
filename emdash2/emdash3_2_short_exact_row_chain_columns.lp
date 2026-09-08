/* Derived column chain pairs and their inclusion from three existing rows. */
require open emdash.emdash3_2_short_exact_rows;
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

// Source-column zero follows from the middle-column zero and the lower mono.
symbol short_exact_row_chain_source_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (r2 : τ (@ComputationalShortExactRow C P t PA A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)))
  (G : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)))
  (middle_zero : τ (@= (Hom C B0 B2)
    (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F)) (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B2)))
  : τ (@= (Hom C A0 A2)
      (@comp_fapp0 C A0 A1 A2 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
      (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A2))
≔ @monic_postcomposition_zero_to_zero_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A2 B2 (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A2 B2 D2 (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)) (@computational_short_exact_monic C P t PA A2 B2 D2 (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) (@computational_short_exact_row_evidence C P t PA A2 B2 D2 r2))
    (@comp_fapp0 C A0 A1 A2 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
    (@eq_trans _ _ _ _
      (@comp_assoc C A0 A1 A2 B2 (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A2 B2 D2 (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C A1 B2) (Hom C A0 B2)
          (λ h : τ (Hom C A1 B2), @comp_fapp0 C A0 A1 B2 h (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
          _ _ (@computational_chain_pair_map_upper_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _ (@comp_assoc C A0 A1 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F)))
          (@eq_trans _ _ _ _
            (@eq_ap (Hom C A0 B1) (Hom C A0 B2)
              (λ h : τ (Hom C A0 B1), @comp_fapp0 C A0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) h)
              _ _ (@computational_chain_pair_map_upper_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
            (@eq_trans _ _ _ _
              (@comp_assoc C A0 B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F) (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0)))
              (@preadditive_precompose_zero_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 B2
                (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F)) (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0)) middle_zero))))));

// Construct the source column from the retained row-map components.
symbol short_exact_row_chain_source_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (r2 : τ (@ComputationalShortExactRow C P t PA A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)))
  (G : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)))
  (middle_zero : τ (@= (Hom C B0 B2)
    (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F)) (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B2)))
  : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 A2)
≔ @computational_chain_pair_intro C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 A2 (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G)
    (@short_exact_row_chain_source_zero_path C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero);

// Construct the middle column using its supplied ordinary chain law.
symbol short_exact_row_chain_middle_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (r2 : τ (@ComputationalShortExactRow C P t PA A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)))
  (G : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)))
  (middle_zero : τ (@= (Hom C B0 B2)
    (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F)) (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B2)))
  : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B1 B2)
≔ @computational_chain_pair_intro C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) middle_zero;

// Its two compatibilities are the existing upper paths of the two row maps.
symbol short_exact_row_chain_inclusion
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (r0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0))
  (r1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1))
  (r2 : τ (@ComputationalShortExactRow C P t PA A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)))
  (G : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)))
  (middle_zero : τ (@= (Hom C B0 B2)
    (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F)) (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B2)))
  : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero) (@short_exact_row_chain_middle_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero))
≔ @computational_chain_pair_map_of_components C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 A1 A2 B0 B1 B2 (@short_exact_row_chain_source_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero) (@short_exact_row_chain_middle_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero)
    (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0)) (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)) (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A2 B2 D2 (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2))
    (@eq_sym _ _ _ (@computational_chain_pair_map_upper_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
    (@computational_chain_pair_map_upper_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G);
