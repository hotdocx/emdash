require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_eq1_evidence_property;

// Lift id through the original kernel of the actual zero differential.
symbol one_cat_zero_kernel_section [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C S t T)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B
  C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))
≔ @one_cat_kernel_family_lift B C S C1 t T T0 P (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  D (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) z;

// The original whole mate reconstructs id.
symbol one_cat_zero_kernel_right_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C S t T)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B
  C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_zero_kernel_section B C S C1 t T T0 P
  D z)) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) D (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) z;

// Kernel cancellation gives the other law for that same section.
symbol one_cat_zero_kernel_left_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C S t T)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B
  C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@one_cat_zero_kernel_section B C S C1 t T T0
  P D z) (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
≔ @one_cat_kernel_family_inclusion_reflect_path B C S C1 t T T0 P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@kernel_adjunction_func C S t T P) D) D (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@one_cat_zero_kernel_section B C S C1 t T T0 P D z) (@kernel_adjunction_family_inclusion_transf B C S t T
  P D)) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S
  t T P) D)) (@eq_trans (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
  S t T P) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P D) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@one_cat_zero_kernel_section B C S C1 t T T0 P D z) (@kernel_adjunction_family_inclusion_transf B C S t T
  P D))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@one_cat_zero_kernel_section B C S C1 t T T0 P D z)) (@kernel_adjunction_family_inclusion_transf B C S t
  T P D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))) (@comp_assoc (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@one_cat_zero_kernel_section B C S C1 t T T0 P D z) (@kernel_adjunction_family_inclusion_transf B C S t T
  P D)) (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (λ u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_src) u (@kernel_adjunction_family_inclusion_transf B C S t T P D))) (@comp_fapp0 (Functor_cat B
  C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@one_cat_zero_kernel_section B C S C1 t T T0 P D z)) (@id (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@one_cat_zero_kernel_right_path B C S C1 t T T0 P D z)));

// Fixed-forward invertibility belongs to the original kernel inclusion.
symbol one_cat_zero_kernel_omega [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C S t T)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B
  C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D))
≔ @omega_equiv_along_intro (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_zero_kernel_section B C S C1 t T T0 P
  D z) (@one_cat_zero_kernel_section B C S C1 t T T0 P D z) (@one_cat_zero_kernel_left_path B C S C1 t
  T T0 P D z) (@one_cat_zero_kernel_right_path B C S C1 t T T0 P D z);
