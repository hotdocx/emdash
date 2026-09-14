/* Ambient equations from the original native source observer. */
require open emdash.emdash3_2_one_cat_kernel_family_projection_paths;
require open emdash.emdash3_2_one_cat_kernel_precomposition;

// The original restricted inclusion reconstructs the original whole source k.
symbol one_cat_kernel_family_lift_ambient_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat
    B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t
    T P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) k)
≔ @eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
  (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T
  P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _
  (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))
  walking_arrow_src) k
    (@eq_sym (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
      (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
      X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
      X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S
      t T P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))
      (@one_cat_kernel_family_projection_path B C S C1 t T P X D (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k
        z)))
    (@one_cat_kernel_family_lift_reconstruction B C S C1 t T T0 P X D k z);

// Whole postcomposition with the original inclusion reflects equality.
symbol one_cat_kernel_family_inclusion_reflect_path
  [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (u v : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
    D))) (p : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
    (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t
    T P D) u) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@kernel_adjunction_family_inclusion_transf B C S t T P D) v)))
  : τ (@= (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))
    u v)
≔ @one_cat_kernel_family_projection_reflect_path B C S C1 t T T0 P X D u v
    (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
      (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
      X D) u) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
      C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@kernel_adjunction_family_inclusion_transf B C S t T P D) u) (@sym_transf_tapp0_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _
      (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src)
      (@one_cat_kernel_family_projection_path B C S C1 t T P X D u)
      (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
        (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
        C S t T P D) u) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@kernel_adjunction_family_inclusion_transf B C S t T P D) v) (@sym_transf_tapp0_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _
        (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
        (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src) p
        (@eq_sym (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
          (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
          (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
          (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
          (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t
          T P) X D) v) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat
          WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) v)
          (@one_cat_kernel_family_projection_path B C S C1 t T P X D v))));

// Specialize to the already constructed kernel-of-composite comparison.
symbol one_cat_kernel_precomposition_square_path
  [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  : τ (@= (@Transf B C (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src))
      (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) (@comp_cat_fapp0 B
        (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src)
        (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t
          T T0 P X D p))
      (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func
        B WalkingArrow_cat C D walking_arrow_src)
        p (@kernel_precomposition_first_transf B C S t T P X D p)))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P
    (@kernel_precomposition_family_func B C S t T P X D p) D
    (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src)
      p (@kernel_precomposition_first_transf B C S t T P X D p))
    (@one_cat_kernel_precomposition_projection_zero_path B C S C1 t T T0 P X D p);
