/* Whole incoming/outgoing row cancellation at the actual original maps. */
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D))
  ⊢ (@one_cat_row_kernel_reconstruction_path B C S C1 t T P A D h) : τ (@= (@Transf B C A (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t
    T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P
    A D h)) (@zero_arrow_family_incoming_transf B C t T A D h));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D))
  ⊢ (@one_cat_row_cokernel_ambient_reconstruction_path B C S C1 t T T0 Q A D h) : τ (@= (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@zero_arrow_family_incoming_func B C t T A D h)))
    (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (u v : τ (@Transf B C X A))
    (p : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
    (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@zero_arrow_family_incoming_transf B C t T A D h) u) (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D h) v)))
  ⊢ (@one_cat_short_exact_family_incoming_reflect_path B C S C1 t T T0 P Q A D h R X u v p) : τ (@= (@Transf B C X A)
    u v);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (Y : τ (Functor B C)) (u v : τ (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)) (p : τ (@= (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) Y u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y v (@diagram_family_transf
    B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  ⊢ (@one_cat_short_exact_family_outgoing_reflect_path B C S C1 t T T0 P Q A D h R Y u v p) : τ (@= (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) u v);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (u v : τ (@Transf B C X A))
  ⊢ (@eq_refl (@Transf B C X A) u) : τ (@= (@Transf B C X A) u v);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (Y : τ (Functor B C)) (u v : τ (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  ⊢ (@eq_refl (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) u) : τ (@= (@Transf B
    C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) u v);
