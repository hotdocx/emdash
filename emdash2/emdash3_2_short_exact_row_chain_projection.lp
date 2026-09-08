/* Quotient/right column and its projection from the actual three rows. */
require open emdash.emdash3_2_short_exact_row_chain_columns;
require open emdash.emdash3_2_hom_factor_chain_zero;

symbol short_exact_row_chain_target_zero_path
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
  : τ (@= (Hom C D0 D2) (@comp_fapp0 C D0 D1 D2 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G) (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F))
      (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) D0 D2))
≔ @hom_precomp_factor_paste_zero_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 D0 B1 D1 B2 D2
    (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0)) (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)) (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A2 B2 D2 (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2)) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G)
    (@computational_chain_pair_map_lower C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F) (@computational_chain_pair_map_lower C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G)
    (@computational_short_exact_epic C P t PA A0 B0 D0 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0)
      (@computational_short_exact_row_evidence C P t PA A0 B0 D0 r0))
    middle_zero;

// Retain the existing right components and the derived zero path.
symbol short_exact_row_chain_target_pair
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
  : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) D0 D1 D2)
≔ @computational_chain_pair_intro C (@additive_preadditive C P t (@preabelian_additive C P t PA)) D0 D1 D2 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F) (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G)
    (@short_exact_row_chain_target_zero_path C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero);

// Both chain-map compatibilities come from the original lower Hom factors.
symbol short_exact_row_chain_projection
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
  : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B1 B2 D0 D1 D2 (@short_exact_row_chain_middle_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero) (@short_exact_row_chain_target_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero))
≔ @computational_chain_pair_map_of_components C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B0 B1 B2 D0 D1 D2 (@short_exact_row_chain_middle_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero) (@short_exact_row_chain_target_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 r0 r1 r2 F G middle_zero)
    (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0)) (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1)) (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A2 B2 D2 (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2))
    (@computational_chain_pair_map_lower_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t PA A0 B0 D0 r0) (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) F) (@eq_sym _ _ _ (@computational_chain_pair_map_lower_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t PA A1 B1 D1 r1) (@computational_short_exact_row_pair C P t PA A2 B2 D2 r2) G));
