/* Two successive coherent row windows; no independently supplied overlap equations. */
require open emdash.emdash3_2_homology_row_spans;
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

symbol s0 ≔ @homology_row_triple_intro I C C1 P t PA T R0 R1 R2 f g z0;
symbol s1 ≔ @homology_row_triple_shift I C C1 P t PA T s0 R3 h z1;
symbol s2 ≔ @homology_row_triple_shift I C C1 P t PA T s1 R4 k z2;
symbol tail1 ≔ @homology_row_span_cons I C C1 P t PA T zero s1 R4 k z2 (@homology_row_span_nil I C C1 P t PA T s2);
symbol tail2 ≔ @homology_row_span_cons I C C1 P t PA T (succ zero) s0 R3 h z1 tail1;
symbol w0 ≔ @homology_window_family_intro I C C1 P t PA T
  (@homology_window_rows_intro I C C1 P t PA T R0 R1 R2 R3 f g h) z0 z1;
symbol w1 ≔ @homology_window_family_intro I C C1 P t PA T
  (@homology_window_rows_intro I C C1 P t PA T R1 R2 R3 R4 g h k) z1 z2;

assert ⊢ @homology_row_triple_row0 I C C1 P t PA T s1 ≡ R1;
assert ⊢ @homology_row_triple_row1 I C C1 P t PA T s1 ≡ R2;
assert ⊢ @homology_row_triple_row2 I C C1 P t PA T s1 ≡ R3;
assert ⊢ @homology_row_triple_first I C C1 P t PA T s1 ≡ g;
assert ⊢ @homology_row_triple_second I C C1 P t PA T s1 ≡ h;
assert ⊢ @homology_row_triple_zero I C C1 P t PA T s1 ≡ z1;
assert ⊢ @homology_row_span_next I C C1 P t PA T (succ zero) s0 tail2 ≡ R3;
assert ⊢ @homology_row_span_map I C C1 P t PA T (succ zero) s0 tail2 ≡ h;
assert ⊢ @homology_row_span_zero I C C1 P t PA T (succ zero) s0 tail2 ≡ z1;
assert ⊢ @homology_row_span_rest I C C1 P t PA T (succ zero) s0 tail2 ≡ tail1;
assert ⊢ @homology_row_span_window I C C1 P t PA T (succ zero) s0 tail2 ≡ w0;
assert ⊢ @homology_row_span_window I C C1 P t PA T zero s1 tail1 ≡ w1;

// The retained maps remain actual transformations with whole Hom action.
constant symbol x : τ (Obj I);
constant symbol y : τ (Obj I);
assert ⊢ @tapp1_func I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T R1)
  (@short_exact_row_family_func I C C1 P t PA T R2) x y
  (@homology_row_triple_first I C C1 P t PA T s1)
  ≡ @tapp1_func I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T R1)
    (@short_exact_row_family_func I C C1 P t PA T R2) x y g;
assert ⊢ @tapp1_func I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T R2)
  (@short_exact_row_family_func I C C1 P t PA T R3) x y
  (@homology_row_span_map I C C1 P t PA T (succ zero) s0 tail2)
  ≡ @tapp1_func I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T R2)
    (@short_exact_row_family_func I C C1 P t PA T R3) x y h;
assertnot ⊢ @homology_row_span_cons I C C1 P t PA T zero s0 R3 h z1 (@homology_row_span_nil I C C1 P t PA T s0)
  : τ (@HomologyRowSpan I C C1 P t PA T (succ zero) s0);
