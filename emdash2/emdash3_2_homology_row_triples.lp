/* Sliding three-row state: whole row functors/maps and the existing chain-zero datum. */
require open emdash.emdash3_2_homology_window_families;
require open emdash.emdash3_2_nat_arithmetic;

constant symbol HomologyRowTriple [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) : Grpd;
constant symbol homology_row_triple_intro [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0)
    (@short_exact_row_family_func I C C1 P t PA T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T R1) (@short_exact_row_family_func I C C1 P t PA T R2)))
  (z : τ (@RowFamilyMiddleChainZero I C C1 P t PA T R0 R1 R2 f g))
  : τ (@HomologyRowTriple I C C1 P t PA T);

symbol homology_row_triple_row0 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) : τ (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_row_triple_row0 _ _ _ _ _ _ _
  (@homology_row_triple_intro _ _ _ _ _ _ _ $R _ _ _ _ _) ↪ $R;

symbol homology_row_triple_row1 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) : τ (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_row_triple_row1 _ _ _ _ _ _ _
  (@homology_row_triple_intro _ _ _ _ _ _ _ _ $R _ _ _ _) ↪ $R;

symbol homology_row_triple_row2 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) : τ (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_row_triple_row2 _ _ _ _ _ _ _
  (@homology_row_triple_intro _ _ _ _ _ _ _ _ _ $R _ _ _) ↪ $R;

symbol homology_row_triple_first [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_row_triple_row0 I C C1 P t PA T state)) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_row_triple_row1 I C C1 P t PA T state)));
rule @homology_row_triple_first _ _ _ _ _ _ _
  (@homology_row_triple_intro _ _ _ _ _ _ _ _ _ _ $v _ _) ↪ $v;

symbol homology_row_triple_second [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_row_triple_row1 I C C1 P t PA T state)) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_row_triple_row2 I C C1 P t PA T state)));
rule @homology_row_triple_second _ _ _ _ _ _ _
  (@homology_row_triple_intro _ _ _ _ _ _ _ _ _ _ _ $v _) ↪ $v;

symbol homology_row_triple_zero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) : τ (@RowFamilyMiddleChainZero I C C1 P t PA T (@homology_row_triple_row0 I C C1 P t PA T state)
    (@homology_row_triple_row1 I C C1 P t PA T state) (@homology_row_triple_row2 I C C1 P t PA T state)
    (@homology_row_triple_first I C C1 P t PA T state) (@homology_row_triple_second I C C1 P t PA T state));
rule @homology_row_triple_zero _ _ _ _ _ _ _
  (@homology_row_triple_intro _ _ _ _ _ _ _ _ _ _ _ _ $v) ↪ $v;

// Shift reuses the two retained rows and their actual whole transformation.
symbol homology_row_triple_shift [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) (R : τ (@ShortExactRowFamily I C C1 P t PA T))
  (h : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_row_triple_row2 I C C1 P t PA T state)) (@short_exact_row_family_func I C C1 P t PA T R)))
  (z : τ (@RowFamilyMiddleChainZero I C C1 P t PA T (@homology_row_triple_row1 I C C1 P t PA T state)
    (@homology_row_triple_row2 I C C1 P t PA T state) R (@homology_row_triple_second I C C1 P t PA T state) h)) : τ
    (@HomologyRowTriple I C C1 P t PA T)
≔ @homology_row_triple_intro I C C1 P t PA T (@homology_row_triple_row1 I C C1 P t PA T state)
  (@homology_row_triple_row2 I C C1 P t PA T state) R (@homology_row_triple_second I C C1 P t PA T state) h z;

symbol homology_row_triple_window [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (state : τ (@HomologyRowTriple I C C1 P t PA
    T)) (R : τ (@ShortExactRowFamily I C C1 P t PA T))
  (h : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_row_triple_row2 I C C1 P t PA T state)) (@short_exact_row_family_func I C C1 P t PA T R)))
  (z : τ (@RowFamilyMiddleChainZero I C C1 P t PA T (@homology_row_triple_row1 I C C1 P t PA T state)
    (@homology_row_triple_row2 I C C1 P t PA T state) R (@homology_row_triple_second I C C1 P t PA T state) h))
  : τ (@HomologyWindowFamily I C C1 P t PA T)
≔ @homology_window_family_intro I C C1 P t PA T
  (@homology_window_rows_intro I C C1 P t PA T (@homology_row_triple_row0 I C C1 P t PA T state)
    (@homology_row_triple_row1 I C C1 P t PA T state) (@homology_row_triple_row2 I C C1 P t PA T state) R
    (@homology_row_triple_first I C C1 P t PA T state) (@homology_row_triple_second I C C1 P t PA T state) h)
  (@homology_row_triple_zero I C C1 P t PA T state) z;
