/* Selected terminal/initial presentations as derived categorical comparisons.
   The original choices provide the existing ordinary adjunction instances;
   all family maps and inverses are constructed by the primary interface.
   These are IsoEvidence definitions, not the retired primitive DefIso
   normalizers. No new universal witness or runtime cancellation is declared. */
require open emdash.emdash3_2_one_cat_terminal_adjunctions;
require open emdash.emdash3_2_one_cat_terminal_adjunction_family_observations;

// Retain the selected original arrow embedding and its actual inverse map.
symbol one_cat_terminal_arrow_family_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F))
≔ @one_cat_terminal_adjunction_family_presentation_evidence B C C1 t
    (@one_cat_terminal_adjunction C C1 t T) F (@terminal_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_terminal_arrow_family_to_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
        (@iso_evidence_to _ _ _ (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) F))
≔ @one_cat_terminal_adjunction_family_presentation_to_src_path B C C1 t
    (@one_cat_terminal_adjunction C C1 t T) F (@terminal_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_terminal_arrow_family_to_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
        (@iso_evidence_to _ _ _ (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_terminal_adjunction_family_presentation_to_tgt_path B C C1 t
    (@one_cat_terminal_adjunction C C1 t T) F (@terminal_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_terminal_arrow_family_from_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
        (@iso_evidence_from _ _ _ (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) F))
≔ @one_cat_terminal_adjunction_family_presentation_from_src_path B C C1 t
    (@one_cat_terminal_adjunction C C1 t T) F (@terminal_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_terminal_arrow_family_from_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
        (@iso_evidence_from _ _ _ (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_terminal_adjunction_family_presentation_from_tgt_path B C C1 t
    (@one_cat_terminal_adjunction C C1 t T) F (@terminal_arrow_transf C t T) h;

// Retain the selected original arrow embedding and its actual inverse map.
symbol one_cat_initial_arrow_family_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F))
≔ @one_cat_initial_adjunction_family_presentation_evidence B C C1 t
    (@one_cat_initial_adjunction C C1 t T) F (@initial_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_initial_arrow_family_to_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)
        (@iso_evidence_to _ _ _ (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_initial_adjunction_family_presentation_to_src_path B C C1 t
    (@one_cat_initial_adjunction C C1 t T) F (@initial_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_initial_arrow_family_to_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)
        (@iso_evidence_to _ _ _ (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) F))
≔ @one_cat_initial_adjunction_family_presentation_to_tgt_path B C C1 t
    (@one_cat_initial_adjunction C C1 t T) F (@initial_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_initial_arrow_family_from_src_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
        (@iso_evidence_from _ _ _ (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) (@Const_func B C t)))
≔ @one_cat_initial_adjunction_family_presentation_from_src_path B C C1 t
    (@one_cat_initial_adjunction C C1 t T) F (@initial_arrow_transf C t T) h;

// Whole endpoint law of the same selected comparison.
symbol one_cat_initial_arrow_family_from_tgt_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
        (@iso_evidence_from _ _ _ (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) F))
≔ @one_cat_initial_adjunction_family_presentation_from_tgt_path B C C1 t
    (@one_cat_initial_adjunction C C1 t T) F (@initial_arrow_transf C t T) h;
