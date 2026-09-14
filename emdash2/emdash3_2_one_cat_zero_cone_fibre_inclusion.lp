require open emdash.emdash3_2_sigma_fibre_inclusion;
require open emdash.emdash3_2_zero_arrow_cones;

// Whole fibre inclusion for the ordinary zero-cone consumer. Its original
// homdc total is unchanged; no general higher duality extension is asserted.
symbol zero_arrow_cone_fibre_inclusion_func [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (a : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (Functor
      (@Transf_cat WalkingArrow_cat C
        (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a) d)
      (@ZeroArrowCone_cat C t T))
≔ @comp_cat_fapp0 (Fibre_cat (@fapp0 (Op_cat C) (Catd_cat (Functor_cat WalkingArrow_cat C))
    (@represented_comma_prof C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) a) d)
    (@Sigma_cat (Functor_cat WalkingArrow_cat C) (@fapp0 (Op_cat C) (Catd_cat (Functor_cat WalkingArrow_cat
    C)) (@represented_comma_prof C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) a))
    (@homdc_total_cat C (Functor_cat WalkingArrow_cat C) (@represented_comma_prof C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))) (@Op_func (Fibre_cat (@homdc_op_edge_catd C
    (Functor_cat WalkingArrow_cat C) (@represented_comma_prof C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T))) a) (@Sigma_cat (Op_cat C) (@homdc_op_edge_catd C (Functor_cat
    WalkingArrow_cat C) (@represented_comma_prof C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)))) (@sigma_fibre_inclusion_func (Op_cat C) (@homdc_op_edge_catd C
    (Functor_cat WalkingArrow_cat C) (@represented_comma_prof C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T))) a)) (@sigma_fibre_inclusion_func (Functor_cat WalkingArrow_cat C)
    (@fapp0 (Op_cat C) (Catd_cat (Functor_cat WalkingArrow_cat C)) (@represented_comma_prof C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) a) d);
