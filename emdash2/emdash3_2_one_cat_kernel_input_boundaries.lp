require open emdash.emdash3_2_one_cat_kernel_input_observation_paths;
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;

// The original whole boundary of the native input reconstructs its original arrow.
symbol one_cat_kernel_input_boundary_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (u : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
  (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) u) (@zero_arrow_family_zero_transf B C t T T0 X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
 : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P X D (@one_cat_kernel_family_input B C C1 t T T0 X D u
  z))) u)
≔ @eq_trans _ _ _ _ (@one_cat_row_kernel_reconstruction_path B C S C1 t T P X D (@one_cat_kernel_family_input B C
  C1 t T T0 X D u z))
  (@one_cat_kernel_family_input_incoming_path B C C1 t T T0 X D u z);
