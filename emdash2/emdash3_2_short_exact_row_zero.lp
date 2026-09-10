/* Outside-support rows: zero middle implies zero at both original endpoints. */
require open emdash.emdash3_2_short_exact_rows;
require open emdash.emdash3_2_preadditive_zero_identity;

symbol short_exact_row_source_identity_zero
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) [A B D : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t PA A B D))
  (zero_B : τ (@= (Hom C B B) (@id C B)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) B B)))
  : τ (@= (Hom C A A) (@id C A)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) A A))
≔ @monic_source_identity_zero C (@computational_homology_preadditive C P t PA) A B
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t PA) A B D
      (@computational_short_exact_row_pair C P t PA A B D row))
    (@computational_short_exact_monic C P t PA A B D
      (@computational_short_exact_row_pair C P t PA A B D row)
      (@computational_short_exact_row_evidence C P t PA A B D row))
    zero_B;

symbol short_exact_row_target_identity_zero
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) [A B D : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t PA A B D))
  (zero_B : τ (@= (Hom C B B) (@id C B)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) B B)))
  : τ (@= (Hom C D D) (@id C D)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) D D))
≔ @epic_target_identity_zero C (@computational_homology_preadditive C P t PA) B D
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t PA) A B D
      (@computational_short_exact_row_pair C P t PA A B D row))
    (@computational_short_exact_epic C P t PA A B D
      (@computational_short_exact_row_pair C P t PA A B D row)
      (@computational_short_exact_row_evidence C P t PA A B D row))
    zero_B;
