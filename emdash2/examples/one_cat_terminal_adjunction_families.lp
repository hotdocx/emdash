/* Primary universality applied to the actual selected terminal/initial
   presentations and native K/Q zero columns. No terminal profile or square
   proofs are supplied by the caller. */
require open emdash.emdash3_2_one_cat_terminal_adjunction_families;
require open emdash.emdash3_2_one_cat_terminal_adjunctions;
require open emdash.emdash3_2_one_cat_adjunction_zero_columns;
// catalog-area: Primary terminal and initial family universality

symbol review_terminal_selected_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F))
≔ @one_cat_terminal_adjunction_family_presentation_evidence B C C1 t
    (@one_cat_terminal_adjunction C C1 t T) F (@terminal_arrow_transf C t T) h;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_to _ _ _ (@review_terminal_selected_family B C C1 t T F h)) walking_arrow_src)
  ≡ @id C (@fapp0 B C F b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_to _ _ _ (@review_terminal_selected_family B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C t;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_from _ _ _ (@review_terminal_selected_family B C C1 t T F h)) walking_arrow_src)
  ≡ @id C (@fapp0 B C F b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_from _ _ _ (@review_terminal_selected_family B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C t;

symbol review_initial_selected_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F))
≔ @one_cat_initial_adjunction_family_presentation_evidence B C C1 t
    (@one_cat_initial_adjunction C C1 t T) F (@initial_arrow_transf C t T) h;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_to _ _ _ (@review_initial_selected_family B C C1 t T F h)) walking_arrow_src)
  ≡ @id C t;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_to _ _ _ (@review_initial_selected_family B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C (@fapp0 B C F b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_from _ _ _ (@review_initial_selected_family B C C1 t T F h)) walking_arrow_src)
  ≡ @id C t;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C _ _
      (@iso_evidence_from _ _ _ (@review_initial_selected_family B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C (@fapp0 B C F b);

// Actual native cokernel zero column, retaining its original whole input diagram.
symbol review_cokernel_zero_column [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (IsoEvidence (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)))
≔ @iso_evidence_comp (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) _ _ _
    (@review_terminal_selected_family (Functor_cat WalkingArrow_cat C) C C1 t T (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@iso_evidence_sym _ _ _
      (@one_cat_diagram_family_reconstruction_evidence (Functor_cat WalkingArrow_cat C) C C1 (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q)));

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
  @iso_evidence_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
    (@review_cokernel_zero_column C S C1 t T T0 Q)
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)));

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
  @iso_evidence_from (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
    (@review_cokernel_zero_column C S C1 t T T0 Q)
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q));

// Actual native kernel zero column, retaining its original whole input diagram.
symbol review_kernel_zero_column [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (IsoEvidence (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)))
≔ @iso_evidence_comp (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) _ _ _
    (@review_initial_selected_family (Functor_cat WalkingArrow_cat C) C C1 t T0 (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_kernel_counit_zero_column_func C S C1 t T P) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@iso_evidence_sym _ _ _
      (@one_cat_diagram_family_reconstruction_evidence (Functor_cat WalkingArrow_cat C) C C1 (@one_cat_kernel_counit_zero_column_func C S C1 t T P)));

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) ⊢
  @iso_evidence_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@review_kernel_zero_column C S C1 t T T0 P)
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)));

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) ⊢
  @iso_evidence_from (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@review_kernel_zero_column C S C1 t T T0 P)
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_zero_column_func C S C1 t T P));
