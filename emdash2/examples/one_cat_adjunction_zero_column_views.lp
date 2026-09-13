/* The actual whole normalized input observes the original differential.
   Components and action are projected from the same whole equality. */
require open emdash.emdash3_2_one_cat_adjunction_zero_column_views;

// cokernel: original whole differential, with no per-diagram equality premise.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢ (@one_cat_cokernel_unit_source_transf_path C S C1 t T T0 Q) : τ (@=
    (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf (Functor_cat
    WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q)
    walking_arrow_src) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
    walking_arrow_generator));
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d : τ (Functor WalkingArrow_cat C))
  ⊢ @eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Hom C (@fapp0
    WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (λ eta : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) d eta) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
    t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0
    Q) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src) (@diagram_evaluation_transf
    WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_cokernel_unit_source_transf_path C S C1 t T T0 Q)
    : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
      (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d (@sym_transf_tapp0_transf
      (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
      (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func
      WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
      (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src)) (@fapp1_fapp0 WalkingArrow_cat C d
      walking_arrow_src walking_arrow_tgt walking_arrow_generator));
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d e : τ (Functor WalkingArrow_cat C))
  ⊢ @eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Functor (Hom_cat
    (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
    WalkingArrow_cat C e walking_arrow_tgt))) (λ eta : τ (@Transf (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt)), @tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e eta)
    (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
    WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
    (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src) (@diagram_evaluation_transf WalkingArrow_cat
    C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_cokernel_unit_source_transf_path C S C1 t T
    T0 Q)
    : τ (@= (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 WalkingArrow_cat C d
      walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt))) (@tapp1_func (Functor_cat WalkingArrow_cat C)
      C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat
      C walking_arrow_tgt) d e (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
      C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t
      T0 Q) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src)) (@tapp1_func (Functor_cat
      WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e (@diagram_evaluation_transf
      WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)));
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d e : τ (Functor WalkingArrow_cat C)) (u : τ (@Transf
    WalkingArrow_cat C d e))
  ⊢ @eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Hom C (@fapp0
    WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt)) (λ eta : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), @tapp1_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) d e eta u) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
    t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0
    Q) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src) (@diagram_evaluation_transf
    WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_cokernel_unit_source_transf_path C S C1 t T T0 Q)
    : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt))
      (@tapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
      WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
      (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src) u) (@tapp1_fapp0 WalkingArrow_cat C d e
      walking_arrow_src walking_arrow_tgt u walking_arrow_generator));
// kernel: original whole differential, with no per-diagram equality premise.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) ⊢ (@one_cat_kernel_counit_target_transf_path C S C1 t T T0 P) : τ (@=
    (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf (Functor_cat
    WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat
    WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t T T0
    P) walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
    walking_arrow_generator));
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (d : τ (Functor WalkingArrow_cat C))
  ⊢ @eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Hom C (@fapp0
    WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (λ eta : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) d eta) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
    (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t T T0 P) walking_arrow_tgt)
    (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_kernel_counit_target_transf_path C S C1 t T T0 P)
    : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
      (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d (@sym_transf_tapp0_transf
      (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0
      (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t T
      T0 P) walking_arrow_tgt)) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt
      walking_arrow_generator));
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (d e : τ (Functor WalkingArrow_cat C))
  ⊢ @eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Functor (Hom_cat
    (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
    WalkingArrow_cat C e walking_arrow_tgt))) (λ eta : τ (@Transf (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt)), @tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e eta)
    (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T
    P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func
    C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S
    C1 t T T0 P) walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) (@one_cat_kernel_counit_target_transf_path C S C1 t T T0 P)
    : τ (@= (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 WalkingArrow_cat C d
      walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt))) (@tapp1_func (Functor_cat WalkingArrow_cat C)
      C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat
      C walking_arrow_tgt) d e (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
      (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
      WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t T T0 P) walking_arrow_tgt)) (@tapp1_func
      (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e (@diagram_evaluation_transf
      WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)));
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (d e : τ (Functor WalkingArrow_cat C)) (u : τ (@Transf WalkingArrow_cat C
    d e))
  ⊢ @eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Hom C (@fapp0
    WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt)) (λ eta : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), @tapp1_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) d e eta u) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
    (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t T T0 P) walking_arrow_tgt)
    (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_kernel_counit_target_transf_path C S C1 t T T0 P)
    : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt))
      (@tapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t
      T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
      (@one_cat_kernel_counit_mate_input C S C1 t T T0 P) walking_arrow_tgt) u) (@tapp1_fapp0 WalkingArrow_cat C d e
      walking_arrow_src walking_arrow_tgt u walking_arrow_generator));
