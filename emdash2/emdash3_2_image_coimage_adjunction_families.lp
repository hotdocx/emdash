/* Whole image/coimage functors from kernel/cokernel adjunctions.
   Arr(κ) and Arr(q) retain the original structural transformations.
   Coim = Q ∘ Arr(κ), Im = K ∘ Arr(q). Their projection/inclusion are
   whole whiskerings of q/κ. No ordinary factor dictionary is involved.
   The canonical Coim⇒Im comparison and its Abelian invertibility are
   separate constructions; they do not follow just from these definitions. */
require open emdash.emdash3_2_kernel_cokernel_adjunctions;

// The naturally varying kernel arrow κ:K⇒ev₀, as a diagram family.
symbol kernel_adjunction_arrow_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (Functor (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@kernel_adjunction_inclusion C S t T P);

// The naturally varying cokernel arrow q:ev₁⇒Q, as a diagram family.
symbol cokernel_adjunction_arrow_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (Functor (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func (Functor_cat WalkingArrow_cat C) C
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
    (@cokernel_adjunction_func C S t T0 Q)
    (@cokernel_adjunction_projection C S t T0 Q);

// Coim(f) = Q(κ_f), with its entire diagram-map action.
symbol adjunction_coimage_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (Functor (Functor_cat WalkingArrow_cat C) C)
≔ @comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@kernel_adjunction_arrow_func C S t T P);

// Im(f) = K(q_f), with its entire diagram-map action.
symbol adjunction_image_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (Functor (Functor_cat WalkingArrow_cat C) C)
≔ @comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P) (@cokernel_adjunction_arrow_func C S t T0 Q);

// π:ev₀⇒Coim is q prewhiskered by Arr(κ).
symbol adjunction_coimage_projection [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@adjunction_coimage_func C S t T T0 P Q))
≔ @fapp0 _ _
    (@comp_cat_con_fapp1_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_arrow_func C S t T P)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
      (@cokernel_adjunction_func C S t T0 Q))
    (@cokernel_adjunction_projection C S t T0 Q);

// ι:Im⇒ev₁ is κ prewhiskered by Arr(q).
symbol adjunction_image_inclusion [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@adjunction_image_func C S t T T0 P Q)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
≔ @fapp0 _ _
    (@comp_cat_con_fapp1_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_arrow_func C S t T0 Q)
      (@kernel_adjunction_func C S t T P)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
    (@kernel_adjunction_inclusion C S t T P);
