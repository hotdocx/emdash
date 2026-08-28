/*
  Thin selected cartesian-category capability.

  A cartesian structure on C is indexed by an already-selected whole binary-
  product functor P : C × C ⊢ C and an already-selected terminal object t.
  It pairs the existing `BinaryProducts(C,P)` and `TerminalObject(C,t)`
  evidence and adds no duplicate runtime rule, unifier, free syntax, or global
  commuting decision procedure.
*/

require open emdash.emdash3_2_triangular_binary_products;
require open emdash.emdash3_2_terminal_objects;

// Selected cartesian structure with binary and empty products.
symbol CartesianCategory
  [C : Cat]
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  : Grpd
≔ @Product_grpd (@BinaryProducts C P) (@TerminalObject C t);

// Constructor pairing the two existing capabilities.
symbol cartesian_category_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (BP : τ (@BinaryProducts C P))
  (T : τ (@TerminalObject C t))
  : τ (@CartesianCategory C P t)
≔ @Product_pair_grpd
    (@BinaryProducts C P)
    (@TerminalObject C t)
    BP T;

// Binary-product evidence projection.
symbol cartesian_binary_products
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (K : τ (@CartesianCategory C P t))
  : τ (@BinaryProducts C P)
≔ sigma_Fst K;

// Terminal-object evidence projection.
symbol cartesian_terminal_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (K : τ (@CartesianCategory C P t))
  : τ (@TerminalObject C t)
≔ sigma_Snd K;
