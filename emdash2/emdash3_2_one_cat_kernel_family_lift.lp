/* Whole kernel lifting at the original diagram family.
   The existing mate is the program; reconstruction and uniqueness follow
   from its inverse and source projection. No ordinary universal dictionary
   or construction-specific naturality input is supplied. */
require open emdash.emdash3_2_one_cat_kernel_family_inputs;
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_paths;

// Apply the original whole kernel mate with D retained as its argument.
symbol one_cat_kernel_family_lift [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))
≔ @fapp0 _ _ (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P) X D) (@one_cat_kernel_family_input B C C1 t T T0 X D k z);

// Its native inverse reconstructs the original whole source k.
symbol one_cat_kernel_family_lift_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P) X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))
    walking_arrow_src) k)
≔ @one_cat_kernel_family_input_source_path B C C1 t T T0 X D k z;

// Whole source reconstruction determines the lift uniquely.
symbol one_cat_kernel_family_lift_unique [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  (b : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
    (p : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
    (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X
    D) b) walking_arrow_src) k))
  : τ (@= (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))
    b (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))
≔ @one_cat_kernel_family_projection_reflect_path B C S C1 t T T0 P X D b (@one_cat_kernel_family_lift B C S C1 t T T0 P
  X D k z)
    (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
      (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
      X D) b) walking_arrow_src) k (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
      WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _
      (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P) X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))
      walking_arrow_src) p
      (@eq_sym (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
        (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
        (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T
        P) X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) walking_arrow_src) k
        (@one_cat_kernel_family_lift_reconstruction B C S C1 t T T0 P X D k z)));
