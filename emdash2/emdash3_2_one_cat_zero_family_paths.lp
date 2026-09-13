/* Whole prewhiskering of zero and annihilation through original family universality.
   These are derived ordinary observations; no additive structure on the
   functor category or caller naturality squares are required. */
require open emdash.emdash3_2_one_cat_cokernel_family_inputs;
require open emdash.emdash3_2_one_cat_adjunction_family_views;
require open emdash.emdash3_2_zero_arrow_family_observations;
require open emdash.emdash3_2_zero_arrow_family_action_paths;

// Prewhiskering preserves the canonical whole zero by initial/terminal uniqueness.
symbol one_cat_zero_family_prewhisker_path [A B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor A B))
  (X Y : τ (Functor B C))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F)) (@fapp1_fapp0 (Functor_cat B C)
    (Functor_cat A C) (@comp_cat_con_func A B C F) X Y (@zero_arrow_family_zero_transf B C t T T0 X Y))
    (@zero_arrow_family_zero_transf A C t T T0 (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F)))
≔ @eq_trans (@Transf A C (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F)) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat A C) (@comp_cat_con_func A B C F) X Y (@zero_arrow_family_zero_transf B C t T T0 X Y)) (@comp_fapp0
  (Functor_cat A C) (@comp_cat_fapp0 A B C X F) (@Const_func A C t) (@comp_cat_fapp0 A B C Y F) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) (@Const_func B C t) Y (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C)
  (@comp_cat_con_func A B C F) X (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@zero_arrow_family_zero_transf A C t T T0 (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A
  B C Y F)) (@fapp1_comp_path (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) X (@Const_func B C t) Y
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@eq_trans
  (@Transf A C (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F)) (@comp_fapp0 (Functor_cat A C)
  (@comp_cat_fapp0 A B C X F) (@Const_func A C t) (@comp_cat_fapp0 A B C Y F) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat A C) (@comp_cat_con_func A B C F) (@Const_func B C t) Y (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A
  B C F) X (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X F) (@Const_func A C t)
  (@comp_cat_fapp0 A B C Y F) (@diagram_family_transf A WalkingArrow_cat C (@comp_cat_fapp0 A C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 A B C Y F)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B
  C F) X (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@zero_arrow_family_zero_transf A C t T T0 (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A
  B C Y F)) (@eq_ap (@Transf A C (@Const_func A C t) (@comp_cat_fapp0 A B C Y F)) (@Transf A C (@comp_cat_fapp0 A B C
  X F) (@comp_cat_fapp0 A B C Y F)) (λ h : τ (@Transf A C (@Const_func A C t) (@comp_cat_fapp0 A B C Y F)),
  (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X F) (@Const_func A C t) (@comp_cat_fapp0 A B C Y F) h
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) X (@Const_func B C t)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) (@Const_func B C t) Y
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@diagram_family_transf A WalkingArrow_cat C (@comp_cat_fapp0 A C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 A B C Y F)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@one_cat_initial_family_arrow_path A C C1 t T0 (@comp_cat_fapp0 A B C Y F) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) (@Const_func B C t) Y (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)))) (@eq_ap (@Transf A C (@comp_cat_fapp0 A B C X F)
  (@Const_func A C t)) (@Transf A C (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F)) (λ h : τ (@Transf A C
  (@comp_cat_fapp0 A B C X F) (@Const_func A C t)), (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X F)
  (@Const_func A C t) (@comp_cat_fapp0 A B C Y F) (@diagram_family_transf A WalkingArrow_cat C (@comp_cat_fapp0 A C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 A B C Y F)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) h)) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func
  A B C F) X (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@diagram_family_transf A WalkingArrow_cat C (@comp_cat_fapp0 A C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 A B C X F)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_family_arrow_path A C C1 t T (@comp_cat_fapp0 A B C X
  F) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) X (@Const_func B C t)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt walking_arrow_generator)))));

// Generic functor action transports a whole annihilation cell.
symbol one_cat_zero_composite_prewhisker_path [A B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor A B))
  (X Y Z : τ (Functor B C))
  (k : τ (@Transf B C X Y))
  (u : τ (@Transf B C Y Z))
  (p : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z u k) (@zero_arrow_family_zero_transf B C t T T0 X
    Z)))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Z F)) (@comp_fapp0 (Functor_cat A C)
    (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F) (@comp_cat_fapp0 A B C Z F) (@fapp1_fapp0 (Functor_cat B
    C) (Functor_cat A C) (@comp_cat_con_func A B C F) Y Z u) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C)
    (@comp_cat_con_func A B C F) X Y k)) (@zero_arrow_family_zero_transf A C t T T0 (@comp_cat_fapp0 A B C X F)
    (@comp_cat_fapp0 A B C Z F)))
≔ @eq_trans (@Transf A C (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Z F)) (@comp_fapp0 (Functor_cat A C)
  (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F) (@comp_cat_fapp0 A B C Z F) (@fapp1_fapp0 (Functor_cat B C)
  (Functor_cat A C) (@comp_cat_con_func A B C F) Y Z u) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C)
  (@comp_cat_con_func A B C F) X Y k)) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F)
  X Z (@comp_fapp0 (Functor_cat B C) X Y Z u k)) (@zero_arrow_family_zero_transf A C t T T0 (@comp_cat_fapp0 A B C X
  F) (@comp_cat_fapp0 A B C Z F)) (@eq_sym (@Transf A C (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Z F))
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) X Z (@comp_fapp0 (Functor_cat B C) X
  Y Z u k)) (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Y F) (@comp_cat_fapp0 A
  B C Z F) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) Y Z u) (@fapp1_fapp0
  (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) X Y k)) (@fapp1_comp_path (Functor_cat B C)
  (Functor_cat A C) (@comp_cat_con_func A B C F) X Y Z u k)) (@eq_trans (@Transf A C (@comp_cat_fapp0 A B C X F)
  (@comp_cat_fapp0 A B C Z F)) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C F) X Z
  (@comp_fapp0 (Functor_cat B C) X Y Z u k)) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B
  C F) X Z (@zero_arrow_family_zero_transf B C t T T0 X Z)) (@zero_arrow_family_zero_transf A C t T T0
  (@comp_cat_fapp0 A B C X F) (@comp_cat_fapp0 A B C Z F)) (@eq_ap (@Transf B C X Z) (@Transf A C (@comp_cat_fapp0 A B
  C X F) (@comp_cat_fapp0 A B C Z F)) (λ h : τ (@Transf B C X Z), (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C)
  (@comp_cat_con_func A B C F) X Z h)) (@comp_fapp0 (Functor_cat B C) X Y Z u k) (@zero_arrow_family_zero_transf B C t
  T T0 X Z) p) (@one_cat_zero_family_prewhisker_path A B C C1 t T T0 F X Z));

// The original whole h:J∘A⇒D derives g∘f=0 by generic naturality and initiality.
symbol one_cat_zero_family_chain_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@= (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat
    B C) A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_incoming_transf B C t T A D h))
    (@zero_arrow_family_zero_transf B C t T T0 A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))
≔ @eq_trans (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
  (Functor_cat B C) A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_incoming_transf B C t T A D h)) (@comp_fapp0
  (Functor_cat B C) A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src))
  (@zero_arrow_family_zero_transf B C t T T0 A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
    (@eq_ap (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C A
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
      (λ v : τ (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0
        (Functor_cat B C) A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat
        C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) v)) (@zero_arrow_family_incoming_transf B C t
        T A D h) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src)
      (eq_refl (@zero_arrow_family_incoming_transf B C t T A D h)))
    (@eq_trans (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
      (Functor_cat B C) A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func
      B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
      walking_arrow_tgt walking_arrow_generator) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
      (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_src)) (@comp_fapp0
      (Functor_cat B C) A (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src
      walking_arrow_tgt walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0 A
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
      (@strict_component_naturality_path WalkingArrow_cat (Functor_cat B C)
        (@sym_func B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
          (@terminal_arrow_diagram_func C t T) A)) (@sym_func B WalkingArrow_cat C D)
        (@sym_func_func_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
          (@terminal_arrow_diagram_func C t T) A) D h)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@eq_ap (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
        (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
        (λ v : τ (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)),
          (@comp_fapp0 (Functor_cat B C) A (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_tgt) v (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
          WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src walking_arrow_tgt
          walking_arrow_generator))) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
          WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_tgt) (@diagram_family_transf B
          WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
          T0) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt
          walking_arrow_generator)
        (@one_cat_initial_family_arrow_path B C C1 t T0 (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_tgt) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
          WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h walking_arrow_tgt))));
