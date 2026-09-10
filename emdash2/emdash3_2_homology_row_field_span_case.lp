/* Expose a constructor's fields before invoking the semantic continuation. */
require open emdash.emdash3_2_homology_row_field_spans;
symbol homology_row_field_span_case [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  [n : τ Nat_grpd] (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g)) [Result : Grpd]
  (branch : Π R3 : τ (@ShortExactRowFamily I C C1 P t PA T), Π h : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R2) (@short_exact_row_family_func I C C1 P t PA T R3)), Π z1 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R1 R2 R3 g h),
    τ (@HomologyRowFieldSpan I C C1 P t PA T n R1 R2 R3 g h z1) → τ Result)
  (span : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ n) R0 R1 R2 f g z0))
  : τ Result;
rule @homology_row_field_span_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $branch
  (@homology_row_field_span_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ $R3 $h $z1 $rest)
  ↪ $branch $R3 $h $z1 $rest;
