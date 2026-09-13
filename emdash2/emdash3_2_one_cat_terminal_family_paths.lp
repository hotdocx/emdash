/* Whole ordinary initial/terminal arrow uniqueness from the existing
   family DefIso normalizers and generic naturality. OneCat(C) remains explicit;
   no stronger higher terminality interface or pointwise premise is introduced. */
require open emdash.emdash3_2_one_cat_terminal_family_universality;
require open emdash.emdash3_2_strict_transfor_component_paths;

// Every whole map F⇒const_t equals the canonical terminal-family differential.
symbol one_cat_terminal_family_arrow_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@= (@Transf B C F (@Const_func B C t)) h (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
    (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator))
≔ @eq_sym (@Transf B C F (@Const_func B C t)) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) h
    (@strict_component_naturality_path WalkingArrow_cat (Functor_cat B C)
      (@sym_func B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h)) (@sym_func B
        WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
        F))
      (@sym_func_func_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@defiso_to _ _
        _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)))
      walking_arrow_src walking_arrow_tgt walking_arrow_generator);

// Every whole map const_t⇒F equals the canonical initial-family differential.
symbol one_cat_initial_family_arrow_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@= (@Transf B C (@Const_func B C t) F) h (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
    (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator))
≔ @eq_sym (@Transf B C (@Const_func B C t) F) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) h
    (@strict_component_naturality_path WalkingArrow_cat (Functor_cat B C)
      (@sym_func B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h)) (@sym_func B
        WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)
        F))
      (@sym_func_func_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@defiso_to _ _ _
        (@one_cat_initial_arrow_family_iso B C C1 t T F h)))
      walking_arrow_src walking_arrow_tgt walking_arrow_generator);
