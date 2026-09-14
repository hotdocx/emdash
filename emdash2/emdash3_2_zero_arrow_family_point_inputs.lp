/* Observe coherent whole input before any kernel/cokernel choice. */
require open emdash.emdash3_2_zero_arrow_cones;

// At x, retain the original (A[x], D[x], h[x]) in the existing native cone.
symbol zero_arrow_family_point_input [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (Obj (@ZeroArrowCone_cat C t T))
≔ (@zero_arrow_cone_obj C t T (@fapp0 K C A x) (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) (@tapp0_fapp0 K
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D x h));
