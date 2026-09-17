/* Terminal/initial specializations of whole diagram-family reflection. */
require open emdash.emdash3_2_one_cat_diagram_family_reflection;
require open emdash.emdash3_2_one_cat_terminal_family_paths;

// For J∘A⇒D, the source endpoint determines the entire map; the other is initial.
symbol one_cat_terminal_family_test_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h k : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (p : τ (@= (@Transf B C A (@sym_fapp0_func B WalkingArrow_cat C D
    walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src) (@sym_transf_tapp0_transf B
    WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D
    k walking_arrow_src)))
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D) h k)
≔ @one_cat_diagram_family_map_path B C C1 (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D h k p (@eq_trans (@Transf B C (@Const_func B C t) (@sym_fapp0_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_tgt)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D k walking_arrow_tgt)
      (@one_cat_initial_family_arrow_path B C C1 t T0 (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_tgt)
        (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_tgt))
      (@eq_sym (@Transf B C (@Const_func B C t) (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_tgt))
        (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) A) D k walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@sym_fapp0_func B
        WalkingArrow_cat C D walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@one_cat_initial_family_arrow_path B C C1 t T0 (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_tgt)
          (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
          (@terminal_arrow_diagram_func C t T) A) D k walking_arrow_tgt))));

// For D⇒I∘A, the target endpoint determines the entire map; the other is terminal.
symbol one_cat_initial_family_test_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h k : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) A))) (p : τ (@= (@Transf B C (@sym_fapp0_func B WalkingArrow_cat C D
    walking_arrow_tgt) A) (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) A) h walking_arrow_tgt) (@sym_transf_tapp0_transf B
    WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) A)
    k walking_arrow_tgt)))
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) A)) h k)
≔ @one_cat_diagram_family_map_path B C C1 D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) A) h k (@eq_trans (@Transf B C (@sym_fapp0_func B WalkingArrow_cat C D
  walking_arrow_src) (@Const_func B C t)) (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) A) h walking_arrow_src)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) A) k walking_arrow_src)
      (@one_cat_terminal_family_arrow_path B C C1 t T (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_src)
        (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) A) h walking_arrow_src))
      (@eq_sym (@Transf B C (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_src) (@Const_func B C t))
        (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) A) k walking_arrow_src) (@diagram_family_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@sym_fapp0_func B
        WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@one_cat_terminal_family_arrow_path B C C1 t T (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_src)
          (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
          (@initial_arrow_diagram_func C t T0) A) k walking_arrow_src)))) p;
