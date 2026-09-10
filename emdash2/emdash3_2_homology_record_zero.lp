/* Zero homology at the retained record, without replacing its object. */
require open emdash.emdash3_2_preadditive_zero_identity;
require open emdash.emdash3_2_homology_record_cancellation;

symbol homology_record_middle_zero
  [C : Cat] (S : τ (@PreadditiveCategory C)) [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair))
  (zero_B : τ (@= (Hom C B B) (@id C B) (@preadditive_hom_zero C S B B)))
  : τ (@= (Hom C (@homology_record_object C S A B D pair H) (@homology_record_object C S A B D pair H))
    (@id C (@homology_record_object C S A B D pair H))
    (@preadditive_hom_zero C S (@homology_record_object C S A B D pair H) (@homology_record_object C S A B D pair
      H)))
≔ @epic_target_identity_zero C S
    (@homology_record_cycle_object C S A B D pair H) (@homology_record_object C S A B D pair H)
    (@homology_record_projection C S A B D pair H) (@homology_record_projection_epic C S A B D pair H)
    (@monic_source_identity_zero C S (@homology_record_cycle_object C S A B D pair H) B
      (@homology_record_cycle_embedding C S A B D pair H) (@homology_record_cycle_monic C S A B D pair H) zero_B);

symbol homology_record_terminal_middle_zero
  [C : Cat] (S : τ (@PreadditiveCategory C)) [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (H : τ (@HomologyRecord C S A B D pair))
  (T : τ (@TerminalObject C B))
  : τ (@= (Hom C (@homology_record_object C S A B D pair H) (@homology_record_object C S A B D pair H))
    (@id C (@homology_record_object C S A B D pair H))
    (@preadditive_hom_zero C S (@homology_record_object C S A B D pair H) (@homology_record_object C S A B D pair
      H)))
≔ @homology_record_middle_zero C S A B D pair H (@preadditive_terminal_identity_zero_path C S B T);
