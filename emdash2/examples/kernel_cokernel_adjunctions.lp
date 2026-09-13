/* Whole universal operations: no W/V or chosen factor spaces are inputs. */
require open emdash.emdash3_2_kernel_cokernel_adjunction_mates;


// A supplied whole functor and adjunction introduce the structure directly.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (K : τ (Functor (Functor_cat WalkingArrow_cat C) C)) (J : τ (@Adjunction C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) K)) ⊢
  @kernel_adjunction_func C S t T (@kernel_adjunction_intro C S t T K J) ≡ K;
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (K : τ (Functor (Functor_cat WalkingArrow_cat C) C)) (J : τ (@Adjunction C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) K)) ⊢
  @kernel_adjunction_evidence C S t T (@kernel_adjunction_intro C S t T K J) ≡ J;

// An arbitrary diagram map uses that whole functor's native action.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (K : τ (Functor (Functor_cat WalkingArrow_cat C) C)) (J : τ (@Adjunction C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) K))
  (d0 d1 : τ (Functor WalkingArrow_cat C)) (eta : τ (Transf d0 d1)) ⊢
  @fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T (@kernel_adjunction_intro C S t T K J)) d0 d1 eta
  ≡ @fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C K d0 d1 eta;


// Whole Hom-functor cancellation and arbitrary-arrow cancellation.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) ⊢ @comp_cat_fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (@kernel_adjunction_unlift_func C S t T U X d) (@kernel_adjunction_lift_func C S t T U X d)
  ≡ @id_func (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d);
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) ⊢ @comp_cat_fapp0 (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (@kernel_adjunction_lift_func C S t T U X d) (@kernel_adjunction_unlift_func C S t T U X d)
  ≡ @id_func (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d));
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) (h : τ (Obj (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))) ⊢
  @fapp0 (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (@kernel_adjunction_unlift_func C S t T U X d) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (@kernel_adjunction_lift_func C S t T U X d) h) ≡ h;
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) (k : τ (Obj (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)))) ⊢
  @fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (@kernel_adjunction_lift_func C S t T U X d) (@fapp0 (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (@kernel_adjunction_unlift_func C S t T U X d) k) ≡ k;

// Cancellation does not identify unrelated arrows of the same Hom.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) (h h' : τ (Obj (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))) ⊢
  @fapp0 (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (@kernel_adjunction_unlift_func C S t T U X d) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (@kernel_adjunction_lift_func C S t T U X d) h) ≡ h';


// The structural arrow is an observation of the actual unit/counit.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U)
  ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U)) (@id_func (Functor_cat WalkingArrow_cat C)) d (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U) (@kernel_adjunction_evidence C S t T U)));


// A supplied whole functor and adjunction introduce the structure directly.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (K : τ (Functor (Functor_cat WalkingArrow_cat C) C)) (J : τ (@Adjunction (Functor_cat WalkingArrow_cat C) C K (@initial_arrow_diagram_func C t T))) ⊢
  @cokernel_adjunction_func C S t T (@cokernel_adjunction_intro C S t T K J) ≡ K;
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (K : τ (Functor (Functor_cat WalkingArrow_cat C) C)) (J : τ (@Adjunction (Functor_cat WalkingArrow_cat C) C K (@initial_arrow_diagram_func C t T))) ⊢
  @cokernel_adjunction_evidence C S t T (@cokernel_adjunction_intro C S t T K J) ≡ J;

// An arbitrary diagram map uses that whole functor's native action.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (K : τ (Functor (Functor_cat WalkingArrow_cat C) C)) (J : τ (@Adjunction (Functor_cat WalkingArrow_cat C) C K (@initial_arrow_diagram_func C t T)))
  (d0 d1 : τ (Functor WalkingArrow_cat C)) (eta : τ (Transf d0 d1)) ⊢
  @fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T (@cokernel_adjunction_intro C S t T K J)) d0 d1 eta
  ≡ @fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C K d0 d1 eta;


// Whole Hom-functor cancellation and arbitrary-arrow cancellation.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) ⊢ @comp_cat_fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (@cokernel_adjunction_uncolift_func C S t T U X d) (@cokernel_adjunction_colift_func C S t T U X d)
  ≡ @id_func (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X));
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) ⊢ @comp_cat_fapp0 (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (@cokernel_adjunction_colift_func C S t T U X d) (@cokernel_adjunction_uncolift_func C S t T U X d)
  ≡ @id_func (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X);
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) (h : τ (Obj (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))) ⊢
  @fapp0 (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (@cokernel_adjunction_uncolift_func C S t T U X d) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (@cokernel_adjunction_colift_func C S t T U X d) h) ≡ h;
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) (k : τ (Obj (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X))) ⊢
  @fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (@cokernel_adjunction_colift_func C S t T U X d) (@fapp0 (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (@cokernel_adjunction_uncolift_func C S t T U X d) k) ≡ k;

// Cancellation does not identify unrelated arrows of the same Hom.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C)) (h h' : τ (Obj (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))) ⊢
  @fapp0 (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (@cokernel_adjunction_uncolift_func C S t T U X d) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (@cokernel_adjunction_colift_func C S t T U X d) h) ≡ h';


// The structural arrow is an observation of the actual unit/counit.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U)
  ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_func C S t T U)) d (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T U)));
