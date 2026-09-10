/* A finite coherent row extension, with overlap fixed in its indices. */
require open emdash.emdash3_2_homology_row_triples;

constant symbol HomologyRowSpan [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (n : τ Nat_grpd) (state : τ (@HomologyRowTriple I C C1 P t PA T)) : Grpd;
constant symbol homology_row_span_nil [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (state : τ (@HomologyRowTriple I C C1 P t PA T)) : τ (@HomologyRowSpan I C C1 P t PA T zero state);
constant symbol homology_row_span_cons [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) [n : τ Nat_grpd] (state : τ (@HomologyRowTriple
    I C C1 P t PA T)) (R : τ (@ShortExactRowFamily I C C1 P t PA T))
  (h : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_row_triple_row2 I C C1 P t PA T state)) (@short_exact_row_family_func I C C1 P t PA T R)))
  (z : τ (@RowFamilyMiddleChainZero I C C1 P t PA T (@homology_row_triple_row1 I C C1 P t PA T state)
    (@homology_row_triple_row2 I C C1 P t PA T state) R (@homology_row_triple_second I C C1 P t PA T state) h))
  (rest : τ (@HomologyRowSpan I C C1 P t PA T n (@homology_row_triple_shift I C C1 P t PA T state R h z)))
  : τ (@HomologyRowSpan I C C1 P t PA T (succ n) state);

symbol homology_row_span_next [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) [n : τ Nat_grpd]
  (state : τ (@HomologyRowTriple I C C1 P t PA T)) (span : τ (@HomologyRowSpan I C C1 P t PA T (succ n) state)) : τ
    (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_row_span_next _ _ _ _ _ _ _ _ _
  (@homology_row_span_cons _ _ _ _ _ _ _ _ _ $R _ _ _) ↪ $R;

symbol homology_row_span_map [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) [n : τ Nat_grpd]
  (state : τ (@HomologyRowTriple I C C1 P t PA T)) (span : τ (@HomologyRowSpan I C C1 P t PA T (succ n) state))
  : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_row_triple_row2
    I C C1 P t PA T state)) (@short_exact_row_family_func I C C1 P t PA T (@homology_row_span_next I C C1 P t PA T n
    state span)));
rule @homology_row_span_map _ _ _ _ _ _ _ _ _
  (@homology_row_span_cons _ _ _ _ _ _ _ _ _ _ $h _ _) ↪ $h;

symbol homology_row_span_zero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) [n : τ Nat_grpd]
  (state : τ (@HomologyRowTriple I C C1 P t PA T)) (span : τ (@HomologyRowSpan I C C1 P t PA T (succ n) state))
  : τ (@RowFamilyMiddleChainZero I C C1 P t PA T (@homology_row_triple_row1 I C C1 P t PA T state)
    (@homology_row_triple_row2 I C C1 P t PA T state) (@homology_row_span_next I C C1 P t PA T n state span)
    (@homology_row_triple_second I C C1 P t PA T state) (@homology_row_span_map I C C1 P t PA T n state span));
rule @homology_row_span_zero _ _ _ _ _ _ _ _ _
  (@homology_row_span_cons _ _ _ _ _ _ _ _ _ _ _ $z _) ↪ $z;

symbol homology_row_span_rest [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) [n : τ Nat_grpd]
  (state : τ (@HomologyRowTriple I C C1 P t PA T)) (span : τ (@HomologyRowSpan I C C1 P t PA T (succ n) state))
  : τ (@HomologyRowSpan I C C1 P t PA T n (@homology_row_triple_shift I C C1 P t PA T state (@homology_row_span_next
    I C C1 P t PA T n state span) (@homology_row_span_map I C C1 P t PA T n state span) (@homology_row_span_zero I C
    C1 P t PA T n state span)));
rule @homology_row_span_rest _ _ _ _ _ _ _ _ _
  (@homology_row_span_cons _ _ _ _ _ _ _ _ _ _ _ _ $rest) ↪ $rest;

// The ordinary four-row window is derived from the sliding state.
symbol homology_row_span_window [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) [n : τ Nat_grpd]
  (state : τ (@HomologyRowTriple I C C1 P t PA T)) (span : τ (@HomologyRowSpan I C C1 P t PA T (succ n) state))
  : τ (@HomologyWindowFamily I C C1 P t PA T)
≔ @homology_row_triple_window I C C1 P t PA T state (@homology_row_span_next I C C1 P t PA T n state span)
  (@homology_row_span_map I C C1 P t PA T n state span) (@homology_row_span_zero I C C1 P t PA T n state span);
