/* Whole endpoint observations of the constructed comparison maps.
   Proofs apply the existing family evaluator's composition law. No caller
   supplies square evidence, and no runtime identity fold is introduced. */
require open emdash.emdash3_2_one_cat_terminal_adjunction_families;

symbol one_cat_terminal_adjunction_family_presentation_to_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@id_func C) (@Const_func C C t))) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@terminal_adjunction_presented_family B C t e F) (@iso_evidence_to _ _ _ (@one_cat_terminal_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_src)
      (@id (Functor_cat B C) F))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@transf_arrow_diagram_func B C F (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@terminal_adjunction_presented_family B C t e F) (@one_cat_diagram_family_reconstruction_to B C C1 (@terminal_adjunction_presented_family B C t e F)) (@one_cat_arrow_family_comparison_to B C C1 F (@Const_func B C t) h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

symbol one_cat_terminal_adjunction_family_presentation_to_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@id_func C) (@Const_func C C t))) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@terminal_adjunction_presented_family B C t e F) (@iso_evidence_to _ _ _ (@one_cat_terminal_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_tgt)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@transf_arrow_diagram_func B C F (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@terminal_adjunction_presented_family B C t e F) (@one_cat_diagram_family_reconstruction_to B C C1 (@terminal_adjunction_presented_family B C t e F)) (@one_cat_arrow_family_comparison_to B C C1 F (@Const_func B C t) h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

symbol one_cat_terminal_adjunction_family_presentation_from_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@id_func C) (@Const_func C C t))) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@iso_evidence_from _ _ _ (@one_cat_terminal_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_src)
      (@id (Functor_cat B C) F))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
    (@terminal_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C F (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@one_cat_arrow_family_comparison_from B C C1 F (@Const_func B C t) h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@one_cat_diagram_family_reconstruction_from B C C1 (@terminal_adjunction_presented_family B C t e F));

symbol one_cat_terminal_adjunction_family_presentation_from_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@id_func C) (@Const_func C C t))) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@iso_evidence_from _ _ _ (@one_cat_terminal_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_tgt)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt
    (@terminal_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C F (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@one_cat_arrow_family_comparison_from B C C1 F (@Const_func B C t) h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@one_cat_diagram_family_reconstruction_from B C C1 (@terminal_adjunction_presented_family B C t e F));

symbol one_cat_initial_adjunction_family_presentation_to_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@Const_func C C t) (@id_func C))) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@initial_adjunction_presented_family B C t e F) (@iso_evidence_to _ _ _ (@one_cat_initial_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_src)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@transf_arrow_diagram_func B C (@Const_func B C t) F (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@initial_adjunction_presented_family B C t e F) (@one_cat_diagram_family_reconstruction_to B C C1 (@initial_adjunction_presented_family B C t e F)) (@one_cat_arrow_family_comparison_to B C C1 (@Const_func B C t) F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_initial_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

symbol one_cat_initial_adjunction_family_presentation_to_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@Const_func C C t) (@id_func C))) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@initial_adjunction_presented_family B C t e F) (@iso_evidence_to _ _ _ (@one_cat_initial_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_tgt)
      (@id (Functor_cat B C) F))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@transf_arrow_diagram_func B C (@Const_func B C t) F (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@initial_adjunction_presented_family B C t e F) (@one_cat_diagram_family_reconstruction_to B C C1 (@initial_adjunction_presented_family B C t e F)) (@one_cat_arrow_family_comparison_to B C C1 (@Const_func B C t) F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_initial_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

symbol one_cat_initial_adjunction_family_presentation_from_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@Const_func C C t) (@id_func C))) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@iso_evidence_from _ _ _ (@one_cat_initial_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_src)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
    (@initial_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C (@Const_func B C t) F (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@one_cat_arrow_family_comparison_from B C C1 (@Const_func B C t) F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_initial_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@one_cat_diagram_family_reconstruction_from B C C1 (@initial_adjunction_presented_family B C t e F));

symbol one_cat_initial_adjunction_family_presentation_from_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@Const_func C C t) (@id_func C))) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@iso_evidence_from _ _ _ (@one_cat_initial_adjunction_family_presentation_evidence B C C1 t J F e h)) walking_arrow_tgt)
      (@id (Functor_cat B C) F))
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt
    (@initial_adjunction_presented_family B C t e F) (@transf_arrow_diagram_func B C (@Const_func B C t) F (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@one_cat_arrow_family_comparison_from B C C1 (@Const_func B C t) F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_initial_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@one_cat_diagram_family_reconstruction_from B C C1 (@initial_adjunction_presented_family B C t e F));
