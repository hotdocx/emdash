/* Derived selected-family comparisons: computed point data, whole endpoint
   laws and both inverse laws. The former primitive DefIso rewrite contract
   is retired; no runtime inverse cut is asserted for this derived evidence. */
require open emdash.emdash3_2_one_cat_terminal_family_universality;
// catalog-area: Primary terminal and initial family universality

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
  ≡ @id C (@fapp0 B C F b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢
  @one_cat_terminal_arrow_family_to_src_path B C C1 t T F h
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) F));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C t;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢
  @one_cat_terminal_arrow_family_to_tgt_path B C C1 t T F h
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) (@Const_func B C t)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
  ≡ @id C (@fapp0 B C F b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢
  @one_cat_terminal_arrow_family_from_src_path B C C1 t T F h
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) F));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C t;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢
  @one_cat_terminal_arrow_family_from_tgt_path B C C1 t T F h
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) (@Const_func B C t)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢
  @iso_evidence_left (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@transf_arrow_diagram_func B C F (@Const_func B C t) h))
      (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)))
      (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢
  @iso_evidence_right (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F))
      (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)))
      (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
  ≡ @id C t;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢
  @one_cat_initial_arrow_family_to_src_path B C C1 t T F h
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) (@Const_func B C t)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C (@fapp0 B C F b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢
  @one_cat_initial_arrow_family_to_tgt_path B C C1 t T F h
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) F));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
  ≡ @id C t;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢
  @one_cat_initial_arrow_family_from_src_path B C C1 t T F h
  : τ (@= (@Transf B C (@Const_func B C t) (@Const_func B C t))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_src)
      (@id (Functor_cat B C) (@Const_func B C t)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C _ _ b
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
  ≡ @id C (@fapp0 B C F b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢
  @one_cat_initial_arrow_family_from_tgt_path B C C1 t T F h
  : τ (@= (@Transf B C F F)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) walking_arrow_tgt)
      (@id (Functor_cat B C) F));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢
  @iso_evidence_left (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@transf_arrow_diagram_func B C (@Const_func B C t) F h))
      (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)))
      (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢
  @iso_evidence_right (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F))
      (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@one_cat_initial_arrow_family_evidence B C C1 t T F h)))
      (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)));

// Retain the original next-Hom action checks at nonidentity base arrows.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t))) (x y : τ (Obj B)) (p q : τ (Hom B x y))
  ⊢ @fapp1_func _ _ (@tapp1_func B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) x y (@iso_evidence_to _ _ _ (@one_cat_terminal_arrow_family_evidence B C C1 t T F h))) p q
    : τ (Functor (Hom_cat (Hom_cat B x y) p q)
      (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) x) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) y))
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) x y (@iso_evidence_to _ _ _ (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) p)
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) x y (@iso_evidence_to _ _ _ (@one_cat_terminal_arrow_family_evidence B C C1 t T F h)) q)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F)) (x y : τ (Obj B)) (p q : τ (Hom B x y))
  ⊢ @fapp1_func _ _ (@tapp1_func B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) x y (@iso_evidence_to _ _ _ (@one_cat_initial_arrow_family_evidence B C C1 t T F h))) p q
    : τ (Functor (Hom_cat (Hom_cat B x y) p q)
      (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) x) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) y))
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) x y (@iso_evidence_to _ _ _ (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) p)
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) x y (@iso_evidence_to _ _ _ (@one_cat_initial_arrow_family_evidence B C C1 t T F h)) q)));
