/* Whole zero-arrow embeddings, with all original selected arrows retained. */
require open emdash.emdash3_2_zero_arrow_diagrams;

// The whole observations recover the actual input functors/transfors.
assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  ⊢ @diagram_family_at_func C WalkingArrow_cat C
      (@terminal_arrow_diagram_func C t T) walking_arrow_src ≡ @id_func C;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  ⊢ @diagram_family_at_func C WalkingArrow_cat C
      (@terminal_arrow_diagram_func C t T) walking_arrow_tgt ≡ @Const_func C C t;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  ⊢ @diagram_family_transf C WalkingArrow_cat C
      (@terminal_arrow_diagram_func C t T)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator
    ≡ @terminal_arrow_transf C t T;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  ⊢ @diagram_family_at_func C WalkingArrow_cat C
      (@initial_arrow_diagram_func C t T) walking_arrow_src ≡ @Const_func C C t;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  ⊢ @diagram_family_at_func C WalkingArrow_cat C
      (@initial_arrow_diagram_func C t T) walking_arrow_tgt ≡ @id_func C;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  ⊢ @diagram_family_transf C WalkingArrow_cat C
      (@initial_arrow_diagram_func C t T)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator
    ≡ @initial_arrow_transf C t T;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (x : τ (Obj C))
  ⊢ @fapp0 WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) x)
      walking_arrow_src ≡ x;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (x : τ (Obj C))
  ⊢ @fapp0 WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) x)
      walking_arrow_tgt ≡ t;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (x : τ (Obj C))
  ⊢ @fapp1_fapp0 WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) x)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator
    ≡ @terminal_arrow_fapp0 C t T x;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) x y p)
    ≡ p;

assertnot (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (x y : τ (Obj C)) (p other : τ (Hom C x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) x y p) ≡ other;

assertnot (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj C)) (p other : τ (Hom C x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) x y p) ≡ other;

// Mixed action of the terminal diagram is the actual whole terminal action.
assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  ⊢ @tapp1_fapp0 WalkingArrow_cat C _ _ walking_arrow_src walking_arrow_tgt
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) x y p) walking_arrow_generator
    ≡ @terminal_arrow_fapp0 C t T x;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  ⊢ @tapp1_fapp0 WalkingArrow_cat C _ _ walking_arrow_src walking_arrow_tgt
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) x y p) walking_arrow_generator
    ≡ @initial_arrow_fapp0 C t T y;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) x y p)
    ≡ @id C t;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  (x : τ (Obj C))
  ⊢ @fapp0 WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) x)
      walking_arrow_src ≡ t;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  (x : τ (Obj C))
  ⊢ @fapp0 WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) x)
      walking_arrow_tgt ≡ x;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  (x : τ (Obj C))
  ⊢ @fapp1_fapp0 WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) x)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator
    ≡ @initial_arrow_fapp0 C t T x;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) x y p)
    ≡ @id C t;

assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) x y p)
    ≡ p;
