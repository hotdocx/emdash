/* Whole ordinary uniqueness observed from the constructed modification.
   Hom(Functor_cat(B,C),F,G) is genuinely discrete under OneCat(C).
   Paths are downstream law evidence; no operational functor is transported. */
require open emdash.emdash3_2_one_cat_terminal_family_universality;
require open emdash.emdash3_2_eq1_hom_action;

symbol one_cat_terminal_family_arrow_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C F (@Const_func B C t)) h
      (@diagram_family_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @hom_to_path (Hom_cat (Functor_cat B C) F (@Const_func B C t))
    ((@one_cat_functor_category B C C1) F (@Const_func B C t)) h _
    (@iso_evidence_to _ _ _
      (@one_cat_terminal_adjunction_family_modification_evidence B C C1 t
        (@one_cat_terminal_adjunction C C1 t T) F h
        (@diagram_family_transf B WalkingArrow_cat C
          (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

symbol one_cat_initial_family_arrow_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C (@Const_func B C t) F) h
      (@diagram_family_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @hom_to_path (Hom_cat (Functor_cat B C) (@Const_func B C t) F)
    ((@one_cat_functor_category B C C1) (@Const_func B C t) F) h _
    (@iso_evidence_to _ _ _
      (@one_cat_initial_adjunction_family_modification_evidence B C C1 t
        (@one_cat_initial_adjunction C C1 t T) F h
        (@diagram_family_transf B WalkingArrow_cat C
          (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)));
