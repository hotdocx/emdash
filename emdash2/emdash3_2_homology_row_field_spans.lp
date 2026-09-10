/* Coherent finite input with the original row/map/zero data retained as rigid indices. */
require open emdash.emdash3_2_homology_row_triples;

constant symbol HomologyRowFieldSpan [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (n : τ Nat_grpd) (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g)) : Grpd;

constant symbol homology_row_field_span_nil [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g)) : τ (@HomologyRowFieldSpan I C C1 P t PA T zero R0 R1 R2 f g z0);

constant symbol homology_row_field_span_cons [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  [n : τ Nat_grpd] (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g))
  (R3 : τ (@ShortExactRowFamily I C C1 P t PA T)) (h : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R2) (@short_exact_row_family_func I C C1 P t PA T R3)))
  (z1 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R1 R2 R3 g h))
  (rest : τ (@HomologyRowFieldSpan I C C1 P t PA T n R1 R2 R3 g h z1))
  : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ n) R0 R1 R2 f g z0);

symbol homology_row_field_span_next [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (n : τ Nat_grpd) (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g))
  (span : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ n) R0 R1 R2 f g z0))
  : τ (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_row_field_span_next _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (@homology_row_field_span_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ $value _ _ _) ↪ $value;

symbol homology_row_field_span_map [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (n : τ Nat_grpd) (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g))
  (span : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ n) R0 R1 R2 f g z0))
  : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R2) (@short_exact_row_family_func I C C1 P t PA T (@homology_row_field_span_next I C C1 P t PA T n R0 R1 R2 f g z0 span)));
rule @homology_row_field_span_map _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (@homology_row_field_span_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $value _ _) ↪ $value;

symbol homology_row_field_span_zero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (n : τ Nat_grpd) (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g))
  (span : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ n) R0 R1 R2 f g z0))
  : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R1 R2 (@homology_row_field_span_next I C C1 P t PA T n R0 R1 R2 f g z0 span) g (@homology_row_field_span_map I C C1 P t PA T n R0 R1 R2 f g z0 span));
rule @homology_row_field_span_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (@homology_row_field_span_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $value _) ↪ $value;

symbol homology_row_field_span_rest [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (n : τ Nat_grpd) (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0) (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g))
  (span : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ n) R0 R1 R2 f g z0))
  : τ (@HomologyRowFieldSpan I C C1 P t PA T n R1 R2 (@homology_row_field_span_next I C C1 P t PA T n R0 R1 R2 f g z0 span) g (@homology_row_field_span_map I C C1 P t PA T n R0 R1 R2 f g z0 span) (@homology_row_field_span_zero I C C1 P t PA T n R0 R1 R2 f g z0 span));
rule @homology_row_field_span_rest _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (@homology_row_field_span_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $value) ↪ $value;
