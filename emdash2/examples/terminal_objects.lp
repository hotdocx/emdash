/*
  Reviewer milestone: whole terminal arrows and contractible incoming homs.

  A selected t carries one whole transformation ! : id_C => const_t. Its
  canonical components and off-diagonal action compute, while every arbitrary
  f : A -> t is propositionally equal to ![A] through recentered
  contractibility. No variable-headed rewrite or bare-variable unifier is
  used, and ![t] remains runtime-distinct from id_t.
*/

require open emdash.emdash3_2_terminal_objects;

// Whole terminal-arrow owner and retained next action.
assert [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) ⊢
  @terminal_arrow_transf C t T
  : τ (Transf (@id_func C) (@Const_func C C t));

assert [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A B : τ (Obj C)) ⊢
  @tapp1_func
    C C
    (@id_func C) (@Const_func C C t)
    A B
    (@terminal_arrow_transf C t T)
  : τ (Functor (Hom_cat C A B) (Hom_cat C A t));

// Canonical off-diagonal action and cut both select ![A].
assert [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A B : τ (Obj C))
  (h : τ (Hom C A B)) ⊢
  @tapp1_fapp0
    C C
    (@id_func C) (@Const_func C C t)
    A B
    (@terminal_arrow_transf C t T)
    h
  ≡ @terminal_arrow_fapp0 C t T A;

assert [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A B : τ (Obj C))
  (h : τ (Hom C A B)) ⊢
  @comp_fapp0 C A B t
    (@terminal_arrow_fapp0 C t T B)
    h
  ≡ @terminal_arrow_fapp0 C t T A;

// Contractibility is recentered at the canonical component.
assert [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Obj C)) ⊢
  @is_contr_center
    (Hom C A t)
    (@terminal_hom_contr_at_arrow C t T A)
  ≡ @terminal_arrow_fapp0 C t T A;

// Došen's (K) equation is a first-class path for every arrow.
assert [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Obj C))
  (f : τ (Hom C A t)) ⊢
  @terminal_unique_path C t T A f
  : τ (@= (Hom C A t) f (@terminal_arrow_fapp0 C t T A));

// The terminal endomorphism agrees propositionally but not at runtime.
assert [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) ⊢
  @terminal_arrow_at_terminal_path C t T
  : τ (@= (Hom C t t)
      (@terminal_arrow_fapp0 C t T t)
      (@id C t));

assertnot [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) ⊢
  @terminal_arrow_fapp0 C t T t ≡ @id C t;
