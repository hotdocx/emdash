/* Native parent view of the existing whole input recovery law. */
require open emdash.emdash3_2_one_cat_kernel_family_inputs;
require open emdash.emdash3_2_zero_arrow_family_observations;
require open emdash.emdash3_2_diagram_reindex_views;

// Compare the parent presentations while the original h remains a variable.
symbol one_cat_native_incoming_parent_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@zero_arrow_family_incoming_transf B C t T X D h)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D h walking_arrow_src))
≔ @eq_refl (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@zero_arrow_family_incoming_transf B C t T X D h);

symbol one_cat_kernel_family_input_incoming_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
    (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) k)
    (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (@zero_arrow_family_incoming_transf B C t T X D (@one_cat_kernel_family_input B C C1 t T T0 X D k z)) k)
≔ @eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@zero_arrow_family_incoming_transf B C t T X D (@one_cat_kernel_family_input B C C1 t T T0 X D k z))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
      D (@one_cat_kernel_family_input B C C1 t T T0 X D k z) walking_arrow_src) k
    (@one_cat_native_incoming_parent_path B C C1 t T X D (@one_cat_kernel_family_input B C C1 t T T0 X D k z))
    (@one_cat_kernel_family_input_source_path B C C1 t T T0 X D k z);
