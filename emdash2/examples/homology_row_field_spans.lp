/* Two successive coherent row windows; no independently supplied overlap equations. */
require open emdash.emdash3_2_homology_row_field_span_case;
constant symbol I : Cat;
constant symbol C : Cat;
constant symbol C1 : τ (IsNCat (cat_succ cat_zero) C);
constant symbol P : τ (Functor (Product_cat C C) C);
constant symbol t : τ (Obj C);
constant symbol PA : τ (@PreAbelianCategory C P t);
constant symbol T : τ (@TerminalObject C t);
constant symbol R0 : τ (@ShortExactRowFamily I C C1 P t PA T);
constant symbol R1 : τ (@ShortExactRowFamily I C C1 P t PA T);
constant symbol R2 : τ (@ShortExactRowFamily I C C1 P t PA T);
constant symbol R3 : τ (@ShortExactRowFamily I C C1 P t PA T);
constant symbol R4 : τ (@ShortExactRowFamily I C C1 P t PA T);
constant symbol f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0)
  (@short_exact_row_family_func I C C1 P t PA T R1));
constant symbol g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1)
  (@short_exact_row_family_func I C C1 P t PA T R2));
constant symbol h : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R2)
  (@short_exact_row_family_func I C C1 P t PA T R3));
constant symbol k : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R3)
  (@short_exact_row_family_func I C C1 P t PA T R4));
constant symbol z0 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g);
constant symbol z1 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R1 R2 R3 g h);
constant symbol z2 : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R2 R3 R4 h k);


symbol rest0 ≔ @homology_row_field_span_nil I C C1 P t PA T R2 R3 R4 h k z2;
symbol rest1 ≔ @homology_row_field_span_cons I C C1 P t PA T zero R1 R2 R3 g h z1 R4 k z2 rest0;
symbol span2 ≔ @homology_row_field_span_cons I C C1 P t PA T (succ zero) R0 R1 R2 f g z0 R3 h z1 rest1;
assert ⊢ @homology_row_field_span_next I C C1 P t PA T (succ zero) R0 R1 R2 f g z0 span2 ≡ R3;
assert ⊢ @homology_row_field_span_map I C C1 P t PA T (succ zero) R0 R1 R2 f g z0 span2 ≡ h;
assert ⊢ @homology_row_field_span_zero I C C1 P t PA T (succ zero) R0 R1 R2 f g z0 span2 ≡ z1;
assert ⊢ @homology_row_field_span_rest I C C1 P t PA T (succ zero) R0 R1 R2 f g z0 span2 ≡ rest1;

symbol case_next ≔ @homology_row_field_span_case I C C1 P t PA T (succ zero) R0 R1 R2 f g z0
  (@ShortExactRowFamily I C C1 P t PA T)
  (λ R : τ (@ShortExactRowFamily I C C1 P t PA T),
   λ m : τ (@Transf I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t PA T R2)
     (@short_exact_row_family_func I C C1 P t PA T R)),
   λ z : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R1 R2 R g m),
   λ rest : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ zero) R1 R2 R g m z),
     R)
  span2;
assert ⊢ case_next ≡ R3;

// The retained map is still a whole transformation, not just a point arrow.
constant symbol x : τ (Obj I);
constant symbol y : τ (Obj I);
assert ⊢ @tapp1_func I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T R2)
  (@short_exact_row_family_func I C C1 P t PA T R3) x y
  (@homology_row_field_span_map I C C1 P t PA T (succ zero) R0 R1 R2 f g z0 span2)
  ≡ @tapp1_func I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T R2)
    (@short_exact_row_family_func I C C1 P t PA T R3) x y h;
assertnot ⊢ rest1 : τ (@HomologyRowFieldSpan I C C1 P t PA T (succ zero) R0 R1 R2 f g z0);
