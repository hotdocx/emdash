/*
  Reviewer milestone: a cartesian capability is exactly selected binary-
  products evidence plus selected terminal-object evidence. It adds no
  duplicate computation.
*/

require open emdash.emdash3_2_cartesian_categories;

assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (BP : τ (@BinaryProducts C P))
  (T : τ (@TerminalObject C t)) ⊢
  @cartesian_category_intro C P t BP T
  : τ (@CartesianCategory C P t);

assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (BP : τ (@BinaryProducts C P))
  (T : τ (@TerminalObject C t)) ⊢
  @cartesian_binary_products
    C P t (@cartesian_category_intro C P t BP T)
  ≡ BP;

assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (BP : τ (@BinaryProducts C P))
  (T : τ (@TerminalObject C t)) ⊢
  @cartesian_terminal_object
    C P t (@cartesian_category_intro C P t BP T)
  ≡ T;
