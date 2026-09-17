/* Whole reflection for walking-arrow families with ordinary target.
   Exchange into Functor_cat(B,C), use the existing diagram reflection, then
   exchange back. This generic owner does not depend on terminal-family
   normalizers. Equality here is observation evidence for whole maps. */
require open emdash.emdash3_2_one_cat_diagram_map_paths;
require open emdash.emdash3_2_one_cat_adjunction_families;

// Whole diagram-family maps agree when both whole endpoint transformations agree.
symbol one_cat_diagram_family_map_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B (Functor_cat WalkingArrow_cat C))]
  (h k : τ (@Transf B (Functor_cat WalkingArrow_cat C) F G))
  (p : τ (@= (@Transf B C
      (@sym_fapp0_func B WalkingArrow_cat C F walking_arrow_src)
      (@sym_fapp0_func B WalkingArrow_cat C G walking_arrow_src))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C F G h walking_arrow_src)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C F G k walking_arrow_src)))
  (q : τ (@= (@Transf B C
      (@sym_fapp0_func B WalkingArrow_cat C F walking_arrow_tgt)
      (@sym_fapp0_func B WalkingArrow_cat C G walking_arrow_tgt))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C F G h walking_arrow_tgt)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C F G k walking_arrow_tgt)))
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) F G) h k)
≔ @eq_ap
    (@Transf WalkingArrow_cat (Functor_cat B C)
      (@sym_func B WalkingArrow_cat C F) (@sym_func B WalkingArrow_cat C G))
    (@Transf B (Functor_cat WalkingArrow_cat C) F G)
    (λ eta : τ (@Transf WalkingArrow_cat (Functor_cat B C)
        (@sym_func B WalkingArrow_cat C F) (@sym_func B WalkingArrow_cat C G)),
      @sym_func_func_transf WalkingArrow_cat B C
        (@sym_func B WalkingArrow_cat C F) (@sym_func B WalkingArrow_cat C G) eta)
    (@sym_func_func_transf B WalkingArrow_cat C F G h)
    (@sym_func_func_transf B WalkingArrow_cat C F G k)
    (@one_cat_diagram_map_path (Functor_cat B C) (@one_cat_functor_category B C C1)
      (@sym_func B WalkingArrow_cat C F) (@sym_func B WalkingArrow_cat C G)
      (@sym_func_func_transf B WalkingArrow_cat C F G h)
      (@sym_func_func_transf B WalkingArrow_cat C F G k) p q);

