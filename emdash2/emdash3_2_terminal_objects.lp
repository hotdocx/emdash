/*
  Selected terminal objects through whole canonical arrows and contractibility.

  A witness is indexed by a chosen object t : C. Its canonical arrows are one
  whole transfor

    ! : id_C => const_t.

  Every Hom_C(A,t) is contractible. Recentring that evidence at ![A] derives
  Došen's unrestricted equation f = ![A] propositionally, without a
  variable-headed rewrite or bare-variable unifier. Runtime computation is
  limited to the canonical-arrow action and cut

    ![B] o h -> ![A].

  The component at t is propositionally equal to id_t through contractibility
  but remains a distinct runtime normal form. This module does not construct
  free cartesian syntax, a global commuting decision procedure, or a
  computational empty weighted-limit comparison.
*/

require open emdash.emdash3_2;

// Selected terminal object indexed by its chosen object t.
injective symbol TerminalObject
  [C : Cat]
  (t : τ (Obj C))
  : Grpd;

// Whole canonical-arrow transfor: ! : id_C => const_t.
symbol terminal_arrow_transf
  [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  : τ (Transf (@id_func C) (@Const_func C C t));

// Stable canonical component ![A] : A -> t.
symbol terminal_arrow_fapp0
  [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Obj C))
  : τ (Hom C A t);

// Component projection from the whole terminal transfor.
rule @tapp0_fapp0
      _ _ _ _ $A
      (@terminal_arrow_transf $C $t $T)
  ↪ @terminal_arrow_fapp0 $C $t $T $A;

// Full off-diagonal terminal action selects the canonical source arrow.
rule @tapp1_fapp0
      _ _ _ _ $A _
      (@terminal_arrow_transf $C $t $T)
      $h
  ↪ @terminal_arrow_fapp0 $C $t $T $A;

// Every hom into t is contractible.
symbol terminal_hom_contr
  [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Obj C))
  : τ (IsContr (Hom C A t));

// Recenter the retained contraction at the whole-transfor component.
symbol terminal_hom_contr_at_arrow
  [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Obj C))
  : τ (IsContr (Hom C A t))
≔ @is_contr_recenter
    (Hom C A t)
    (@terminal_hom_contr C t T A)
    (@terminal_arrow_fapp0 C t T A);

// Došen's unrestricted (K) equation is propositional: f = ![A].
symbol terminal_unique_path
  [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  [A : τ (Obj C)]
  (f : τ (Hom C A t))
  : τ (@= (Hom C A t) f (@terminal_arrow_fapp0 C t T A))
≔ @eq_sym
    (Hom C A t)
    (@terminal_arrow_fapp0 C t T A)
    f
    (@is_contr_path
      (Hom C A t)
      (@terminal_hom_contr_at_arrow C t T A)
      f);

// Canonical terminal cut: ![B] o h -> ![A].
rule @comp_fapp0
      $C $A $B _
      (@terminal_arrow_fapp0 $C $t $T $B)
      $h
  ↪ @terminal_arrow_fapp0 $C $t $T $A;

// The canonical endomorphism of t is propositionally the identity.
symbol terminal_arrow_at_terminal_path
  [C : Cat]
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  : τ (@= (Hom C t t)
      (@terminal_arrow_fapp0 C t T t)
      (@id C t))
≔ @eq_sym
    (Hom C t t)
    (@id C t)
    (@terminal_arrow_fapp0 C t T t)
    (@terminal_unique_path C t T t (@id C t));
