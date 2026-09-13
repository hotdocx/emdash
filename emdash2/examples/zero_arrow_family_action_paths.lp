/* Proof-time sufficient comparisons retain all whole data and indices. */
require open emdash.emdash3_2_zero_arrow_family_action_paths;

// Same whole map through raw versus represented parent-family annotations.
assert (B C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  ⊢ eq_refl (@sym_transf_tapp0_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src)
    : τ (@= (@Transf B C A (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_src))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C
        (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A)
        D h walking_arrow_src));

assertnot (B C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h k : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  ⊢ eq_refl (@sym_transf_tapp0_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src)
    : τ (@= (@Transf B C A (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_src))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C
        (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A)
        D k walking_arrow_src));

// Equal endpoint functors do not identify the two shape observations of h.
assertnot (B C : Cat) (F : τ (Functor B C)) (eta : τ (@Transf B C F F))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func B C F F eta) (@transf_arrow_diagram_func B C F F eta)))
  ⊢ eq_refl (@sym_transf_tapp0_transf B WalkingArrow_cat C
      (@transf_arrow_diagram_func B C F F eta) (@transf_arrow_diagram_func B C F F eta) h walking_arrow_src)
    : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C
        (@transf_arrow_diagram_func B C F F eta) (@transf_arrow_diagram_func B C F F eta) h walking_arrow_src)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C
        (@transf_arrow_diagram_func B C F F eta) (@transf_arrow_diagram_func B C F F eta) h walking_arrow_tgt));
