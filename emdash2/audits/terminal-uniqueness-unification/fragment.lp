// Non-library review fragment: append to a full terminal_objects owner copy.
unif_rule $f ≡ @terminal_arrow_fapp0 $C $t $T $A ↪ [tt ≡ tt];

assert [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  [A : τ (Obj C)] (f : τ (Hom C A t)) ⊢
  @eq_refl (Hom C A t) f
  : τ (@= (Hom C A t) f (@terminal_arrow_fapp0 C t T A));

assertnot [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  [A : τ (Obj C)] (f : τ (Hom C A t)) ⊢
  f ≡ @terminal_arrow_fapp0 C t T A;
