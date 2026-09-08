/*
  Whole terminal/initial arrow embeddings for the kernel/cokernel interface.

  X↦(X→t) uses TerminalObject(C,t). The direct dual X↦(t→X) uses the
  explicitly supplied TerminalObject(Op(C),t), with its transfor obtained by
  Op_transf. These definitions introduce no new zero-object capability or
  adjunction and do not infer whole dual structure from objectwise proofs.
*/
require open emdash.emdash3_2_arrow_diagram_families;
require open emdash.emdash3_2_terminal_objects;

// J:C→Arr(C), X↦(X→t), from the existing whole terminal-arrow transformation.
symbol terminal_arrow_diagram_func
  [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  : τ (Functor C (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func C C (@id_func C) (@Const_func C C t)
    (@terminal_arrow_transf C t T);

// The whole dual arrow transformation const_t⇒id_C, transparently via Op.
symbol initial_arrow_transf
  [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  : τ (@Transf C C (@Const_func C C t) (@id_func C))
≔ @Op_transf (Op_cat C) (Op_cat C)
    (@id_func (Op_cat C)) (@Const_func (Op_cat C) (Op_cat C) t)
    (@terminal_arrow_transf (Op_cat C) t T);

// Native-C typed component view; the body remains the original dual arrow.
symbol initial_arrow_fapp0
  [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (x : τ (Obj C))
  : τ (Hom C t x)
≔ @terminal_arrow_fapp0 (Op_cat C) t T x;

// I:C→Arr(C), X↦(t→X); this is the direct dual, not a second arrow calculus.
symbol initial_arrow_diagram_func
  [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  : τ (Functor C (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func C C (@Const_func C C t) (@id_func C)
    (@initial_arrow_transf C t T);
