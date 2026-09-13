/* Whole Coim/Im retain their adjunction selections and native action.
   Assertions are reviewer observations, not theory-level equality premises. */
require open emdash.emdash3_2_image_coimage_adjunction_families;

// Whole arrow observation recovers the original structural transformation.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ @diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T P)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ (@kernel_adjunction_inclusion C S t T P);

// Whole arrow observation recovers the original structural transformation.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ @diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@cokernel_adjunction_arrow_func C S t T0 Q)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ (@cokernel_adjunction_projection C S t T0 Q);

// An arbitrary diagram map retains its corresponding original component.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C)) (u : τ (@Transf WalkingArrow_cat C d e))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) d e u)
    ≡ (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) d e u);

// An arbitrary diagram map retains its corresponding original component.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C)) (u : τ (@Transf WalkingArrow_cat C d e))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) d e u)
    ≡ @tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src u;

// An arbitrary diagram map retains its corresponding original component.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C)) (u : τ (@Transf WalkingArrow_cat C d e))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) d e u)
    ≡ @tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt u;

// An arbitrary diagram map retains its corresponding original component.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C)) (u : τ (@Transf WalkingArrow_cat C d e))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) d e u)
    ≡ (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) d e u);

// The coimage object is evaluated at the actual whole structural arrow.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d : τ (Functor WalkingArrow_cat C))
  ⊢ (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d)
    ≡ @fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
      (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) d);

// The whole coimage Hom action composes the original two Hom functors.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C))
  ⊢ @fapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d e
    ≡ @comp_cat_fapp0 _ _ _
      (@fapp1_func (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) e))
      (@fapp1_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) d e);

// The coimage structural component is the original adjunction component.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d : τ (Functor WalkingArrow_cat C))
  ⊢ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@adjunction_coimage_projection C S t T T0 P Q)
    ≡ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) d) (@cokernel_adjunction_projection C S t T0 Q);

// The coimage structural transformation keeps its next Hom action.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C))
  (u v : τ (@Transf WalkingArrow_cat C d e))
  ⊢ @fapp1_func (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) d e (@adjunction_coimage_projection C S t T T0 P Q)) u v
    : τ (Functor (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) d e) u v)
      (Hom_cat (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) e)) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) d e (@adjunction_coimage_projection C S t T T0 P Q)) u)
        (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) d e (@adjunction_coimage_projection C S t T T0 P Q)) v)));

// The image object is evaluated at the actual whole structural arrow.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d : τ (Functor WalkingArrow_cat C))
  ⊢ (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) d)
    ≡ @fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
      (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) d);

// The whole image Hom action composes the original two Hom functors.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C))
  ⊢ @fapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) d e
    ≡ @comp_cat_fapp0 _ _ _
      (@fapp1_func (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) e))
      (@fapp1_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) d e);

// The image structural component is the original adjunction component.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d : τ (Functor WalkingArrow_cat C))
  ⊢ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@adjunction_image_inclusion C S t T T0 P Q)
    ≡ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) d) (@kernel_adjunction_inclusion C S t T P);

// The image structural transformation keeps its next Hom action.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (d e : τ (Functor WalkingArrow_cat C))
  (u v : τ (@Transf WalkingArrow_cat C d e))
  ⊢ @fapp1_func (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e (@adjunction_image_inclusion C S t T T0 P Q)) u v
    : τ (Functor (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) d e) u v)
      (Hom_cat (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) e)) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e (@adjunction_image_inclusion C S t T T0 P Q)) u)
        (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d e) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) e)) (@tapp1_func (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) d e (@adjunction_image_inclusion C S t T T0 P Q)) v)));

// Independent kernel selections do not collapse to one coimage functor.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (P1 : τ (@KernelAdjunctionStructure C S t T))
  ⊢ (@adjunction_coimage_func C S t T T0 P Q) ≡ @adjunction_coimage_func C S t T T0 P1 Q;

// Independent cokernel selections do not collapse to one image functor.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (Q1 : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@adjunction_image_func C S t T T0 P Q) ≡ @adjunction_image_func C S t T T0 P Q1;
