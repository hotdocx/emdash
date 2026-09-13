/* Whole incoming-arrow observations of h:J∘A⇒D, before universal selection. */
require open emdash.emdash3_2_zero_arrow_diagrams;

// Observe the same h at the source endpoint, retaining its native parent family.
symbol zero_arrow_family_incoming_transf [B C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
≔ (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  A) D h walking_arrow_src);

// Introduce that whole incoming transformation as its original arrow family.
symbol zero_arrow_family_incoming_func [B C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@zero_arrow_family_incoming_transf B C t T A D h);
