/* The actual defined Coim⇒Im, its whole factorization and retained action.
   All structures below remain arbitrary parameters. The optional raw formula
   is a reviewer observation of the original whole mate, not its runtime owner. */
require open emdash.emdash3_2_one_cat_image_coimage_comparison;

// Native whole mating agrees with the original cokernel-family formula.
symbol review_comparison_raw_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)
    (@cokernel_adjunction_family_colift_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
    (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q)))
≔ (@one_cat_adjunction_family_untranspose_agrees (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
  T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))
  (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q));

// The public signature retains the original selected Coim and Im.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) : τ (@Transf (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q));

// Native inverse mating reconstructs the entire constructed input.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ @fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) C
      (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
        (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat
        (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat
        C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)))
        (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)
    ≡ (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q);

// The whole target of that input is the original u.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@one_cat_coimage_image_input_target_path C S C1 t T T0 P Q) : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat
    C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C)
    C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q)
    walking_arrow_tgt) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q));

// The native whole factorization reconstructs ∂.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@one_cat_coimage_image_factorization_path C S C1 t T T0 P Q) : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt)) (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@diagram_evaluation_transf WalkingArrow_cat C
    walking_arrow_src walking_arrow_tgt walking_arrow_generator));

// A competing whole factorization equals the actual comparison.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (b : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P
    Q))) (p : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q b) (@diagram_evaluation_transf WalkingArrow_cat C
    walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  ⊢ (@one_cat_coimage_image_factorization_unique C S C1 t T T0 P Q b p) : τ (@= (@Transf (Functor_cat WalkingArrow_cat
    C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)) b
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q));

// The canonical factorization proof does not certify an unrelated candidate.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (b : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P
    Q)))
  ⊢ (@one_cat_coimage_image_factorization_path C S C1 t T T0 P Q) : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt)) (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q b) (@diagram_evaluation_transf
    WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator));

// Native cancellation does not reconstruct an unrelated input.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (other : τ (@Transf
    (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func
    C t T0) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)))))
  ⊢  @fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) C
      (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
        (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat
        (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat
        C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)))
        (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)
     ≡ other;

// The actual component retains both original selected endpoints.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d : τ (Functor
    WalkingArrow_cat C))
  ⊢ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
    S t T T0 P Q) d)) (λ z : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)), (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d z))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@cokernel_adjunction_family_colift_transf (Functor_cat
    WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))
    (@review_comparison_raw_path C S C1 t T T0 P Q)) : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
    S t T T0 P Q) d)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) d (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@tapp0_fapp0
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P
    Q) d (@cokernel_adjunction_family_colift_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
    (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))));

// The entire off-diagonal Hom functor agrees with the original whole formula.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d e : τ (Functor
    WalkingArrow_cat C))
  ⊢ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C
    (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) e))) (λ z : τ (@Transf (Functor_cat WalkingArrow_cat
    C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)), (@tapp1_func (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e z))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@cokernel_adjunction_family_colift_transf (Functor_cat
    WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))
    (@review_comparison_raw_path C S C1 t T T0 P Q)) : τ (@= (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) d e)
    (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) e))) (@tapp1_func (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e
    (@cokernel_adjunction_family_colift_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
    (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))));

// An arbitrary original diagram map retains the same mixed action.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d e : τ (Functor
    WalkingArrow_cat C)) (m : τ (@Transf WalkingArrow_cat C d e))
  ⊢ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
    S t T T0 P Q) e)) (λ z : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)), (@tapp1_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e z m))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@cokernel_adjunction_family_colift_transf (Functor_cat
    WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))
    (@review_comparison_raw_path C S C1 t T T0 P Q)) : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
    S t T T0 P Q) e)) (@tapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) d e (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) m) (@tapp1_fapp0
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P
    Q) d e (@cokernel_adjunction_family_colift_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
    (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q)) m));

// The factorization recovers the original differential at an arbitrary diagram.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d : τ (Functor
    WalkingArrow_cat C))
  ⊢ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Hom C (@fapp0
    WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (λ z : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), (@tapp0_fapp0 (Functor_cat WalkingArrow_cat
    C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_tgt) d z)) (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@diagram_evaluation_transf WalkingArrow_cat C
    walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_coimage_image_factorization_path C S C1 t T
    T0 P Q)) : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d
    walking_arrow_tgt)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat
    C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d
    (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q (@one_cat_coimage_image_comparison C S C1 t T T0 P
    Q))) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d
    (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// Factorization retains the differential Hom functor at arbitrary diagrams.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (d e : τ (Functor
    WalkingArrow_cat C))
  ⊢ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (Functor (Hom_cat
    (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
    WalkingArrow_cat C e walking_arrow_tgt))) (λ z : τ (@Transf (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt)), (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat
    C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e z))
    (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q (@one_cat_coimage_image_comparison C S C1 t T T0 P
    Q)) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_coimage_image_factorization_path C S C1 t T T0 P Q)) : τ (@= (Functor (Hom_cat (Functor_cat
    WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
    walking_arrow_tgt))) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat
    C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e
    (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q (@one_cat_coimage_image_comparison C S C1 t T T0 P
    Q))) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e
    (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// The next Hom functor, with its dependent endpoints, stays one native arrow.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C)) (m n : τ (@Transf WalkingArrow_cat C d e))
  ⊢ @eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (Obj (@LaxArrow_cat Cat_cat)) (λ z : τ (@Transf (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)),
    (@lax_edge Cat_cat (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) d e) m n) (Hom_cat (Hom_cat C (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) e)) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat
    C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e z) m)
    (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
    S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) d e z) n)) (@fapp1_func (Hom_cat (Functor_cat WalkingArrow_cat C) d e)
    (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e z) m
    n))) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@cokernel_adjunction_family_colift_transf (Functor_cat
    WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))
    (@review_comparison_raw_path C S C1 t T T0 P Q)
    : τ (@= (Obj (@LaxArrow_cat Cat_cat)) (@lax_edge Cat_cat (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) d e) m
      n) (Hom_cat (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d)
      (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) e)) (@fapp0 (Hom_cat
      (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
      C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
      (@adjunction_image_func C S t T T0 P Q) d e (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) m) (@fapp0
      (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
      C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
      (@adjunction_image_func C S t T T0 P Q) d e (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) n))
      (@fapp1_func (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C)
      C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C
      (@adjunction_image_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e
      (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) m n)) (@lax_edge Cat_cat (Hom_cat (Hom_cat (Functor_cat
      WalkingArrow_cat C) d e) m n) (Hom_cat (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
      C S t T T0 P Q) e)) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat
      WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C
      (@adjunction_image_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e
      (@cokernel_adjunction_family_colift_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
      (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
      WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
      WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))) m) (@fapp0
      (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
      C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
      (@adjunction_image_func C S t T T0 P Q) d e (@cokernel_adjunction_family_colift_transf (Functor_cat
      WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat
      WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
      (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func
      C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P
      Q))) n)) (@fapp1_func (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat
      WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C
      (@adjunction_image_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d e
      (@cokernel_adjunction_family_colift_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
      (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
      WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
      WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q))) m n)));
