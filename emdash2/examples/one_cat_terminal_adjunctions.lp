/* Reviewer: whole one cat terminal adjunctions data and qualified computation. */
require open emdash.emdash3_2_one_cat_terminal_adjunctions;
// catalog-area: Categorical contraction and ordinary terminal adjunctions

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (x : τ (Obj C)) ⊢
 @sym_transf_tapp0_transf C WalkingArrow_cat C _ _
   (@defiso_to _ _ _ (@one_cat_terminal_adjunction_diagram_iso C C1 t T)) walking_arrow_src
 ≡ @id (Functor_cat C C) (@id_func C);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject (Op_cat C) t)) ⊢
 @sym_transf_tapp0_transf C WalkingArrow_cat C _ _
   (@defiso_from _ _ _ (@one_cat_initial_adjunction_diagram_iso C C1 t T)) walking_arrow_tgt
 ≡ @id (Functor_cat C C) (@id_func C);

// Both whole functor cuts compute, retaining this adjunction's mate data.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (x : τ (Obj C)) ⊢
  @comp_cat_fapp0 (Hom_cat C x t) Terminal_cat (Hom_cat C x t) (@defiso_from Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x))
  ≡ @id_func (Hom_cat C x t);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (x : τ (Obj C)) ⊢
  @comp_cat_fapp0 Terminal_cat (Hom_cat C x t) Terminal_cat (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) (@defiso_from Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x))
  ≡ @id_func Terminal_cat;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (x : τ (Obj C)) (h : τ (Obj (Hom_cat C x t))) ⊢
  @fapp0 Terminal_cat (Hom_cat C x t) (@defiso_from Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) (@fapp0 (Hom_cat C x t) Terminal_cat (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) h)
  ≡ h;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_inv Cat_cat (Hom_cat C x t) Terminal_cat (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) (@one_cat_terminal_hom_equivalence C C1 t T x)
  ≡ (@defiso_from Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_inv Cat_cat (Hom_cat C x t) Terminal_cat (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) (@one_cat_terminal_hom_equivalence C C1 t T x)
  ≡ (@defiso_from Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (x : τ (Obj C)) ⊢
  @is_contr_center (Obj (Hom_cat C x t)) (@one_cat_terminal_hom_contraction C C1 t T x)
  ≡ @fapp0 Terminal_cat (Hom_cat C x t) (@defiso_from Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) Terminal_obj;

// The Hom comparison retains an iterated Hom functor, not just a point map.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (x : τ (Obj C)) (h k : τ (Obj (Hom_cat C x t))) ⊢
  @fapp1_func (Hom_cat C x t) Terminal_cat (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)) h k
  : τ (Functor (Hom_cat (Hom_cat C x t) h k) Terminal_cat);

// Both whole functor cuts compute, retaining this adjunction's mate data.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢
  @comp_cat_fapp0 (Hom_cat C t x) Terminal_cat (Hom_cat C t x) (@defiso_from Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x))
  ≡ @id_func (Hom_cat C t x);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢
  @comp_cat_fapp0 Terminal_cat (Hom_cat C t x) Terminal_cat (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) (@defiso_from Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x))
  ≡ @id_func Terminal_cat;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) (h : τ (Obj (Hom_cat C t x))) ⊢
  @fapp0 Terminal_cat (Hom_cat C t x) (@defiso_from Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) (@fapp0 (Hom_cat C t x) Terminal_cat (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) h)
  ≡ h;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_inv Cat_cat (Hom_cat C t x) Terminal_cat (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) (@one_cat_initial_hom_equivalence C C1 t T x)
  ≡ (@defiso_from Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢
  @omega_equiv_along_right_inv Cat_cat (Hom_cat C t x) Terminal_cat (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) (@one_cat_initial_hom_equivalence C C1 t T x)
  ≡ (@defiso_from Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢
  @is_contr_center (Obj (Hom_cat C t x)) (@one_cat_initial_hom_contraction C C1 t T x)
  ≡ @fapp0 Terminal_cat (Hom_cat C t x) (@defiso_from Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) Terminal_obj;

// The Hom comparison retains an iterated Hom functor, not just a point map.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) (h k : τ (Obj (Hom_cat C t x))) ⊢
  @fapp1_func (Hom_cat C t x) Terminal_cat (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)) h k
  : τ (Functor (Hom_cat (Hom_cat C t x) h k) Terminal_cat);

// No migration of the original terminal normal form is installed.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) ⊢
  @terminal_arrow_fapp0 C t T t ≡ @id C t;

// The whole adjunction unit remains an independent computational owner.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) ⊢
  @one_cat_terminal_adjunction_unit C C1 t T ≡ @terminal_arrow_transf C t T;

// Whole profunctor cancellation precedes any point observation.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) ⊢
  @comp_fapp0 (Prof_cat C Terminal_cat) _ _ _
    (@defiso_from _ _ _ (@Adjunction_hom_prof_comparison C Terminal_cat
      (Terminal_func C) (@Obj_func C t) (@one_cat_terminal_adjunction C C1 t T)))
    (@defiso_to _ _ _ (@Adjunction_hom_prof_comparison C Terminal_cat
      (Terminal_func C) (@Obj_func C t) (@one_cat_terminal_adjunction C C1 t T)))
  ≡ @id (Prof_cat C Terminal_cat)
      (@Hom_prof_along C Terminal_cat Terminal_cat (Terminal_func C) (@id_func Terminal_cat));
