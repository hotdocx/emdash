/* Native whole-family mates consume the original normalized unit/counit.
   These tests retain the actual K/Q choices and coherent input families.
   Equality with the older raw whole factor formulas is a separate boundary. */
require open emdash.emdash3_2_one_cat_adjunction_families;
require open emdash.emdash3_2_one_cat_adjunction_zero_columns;

// The image factor has the original selected endpoints.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
    (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q))
    (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q))
    : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@adjunction_image_func C S t T T0 P Q));

// The entire original coherent input is recovered, before taking components.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢ (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func
    (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C
    C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q))
    (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
    (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q))
    (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q))) ≡ (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q);
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d : τ (Functor WalkingArrow_cat C))
  ⊢ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat
    WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q) d
    (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
    (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@fapp0 _ _
    (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
    t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q)))
    ≡ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat
      WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q) d
      (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q);

// The coimage factor has the original selected endpoints.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
    T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t
    T T0 P))
    : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt));

// The entire original coherent input is recovered, before taking components.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢ (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
    (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0
    Q) (@kernel_adjunction_arrow_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
    T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t
    T T0 P))) ≡ (@one_cat_kernel_counit_mate_input C S C1 t T T0 P);
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d : τ (Functor WalkingArrow_cat C))
  ⊢ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t
    T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) d (@fapp0 _
    _ (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
    T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
    T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t
    T T0 P)))
    ≡ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S
      t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) d
      (@one_cat_kernel_counit_mate_input C S C1 t T T0 P);
