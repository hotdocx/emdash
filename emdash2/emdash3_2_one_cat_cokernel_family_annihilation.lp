require open emdash.emdash3_2_one_cat_cokernel_family_projection_paths;
require open emdash.emdash3_2_one_cat_zero_family_paths;
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_paths;
require open emdash.emdash3_2_product_family_action_views;

// Terminal-family uniqueness preserves the original source presentation.
symbol one_cat_cokernel_family_zero_view_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q
  : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@zero_arrow_family_zero_transf B
  C t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
  Q) D)) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  D)))
≔ @eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@Const_func B C t))
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (λ h : τ (@Transf B C (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src) (@Const_func B C t)), (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@Const_func B C t) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D))
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) h)) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D))
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@one_cat_terminal_family_arrow_path B C C1 t T (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) D)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator));

// Restrict the original whole cokernel annihilation to the actual diagram family.
symbol one_cat_cokernel_family_annihilation_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
  Q) D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@diagram_family_transf B WalkingArrow_cat
  C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)))
≔ @eq_trans _ _ _ _ (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (λ h : τ (@Transf B C (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)), (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) h
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q))
  (@one_cat_cokernel_family_projection_whisker_path B C S C1 t T0 Q D)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (λ h : τ
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)) (@cokernel_adjunction_projection C S t T0 Q)) h))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@one_cat_diagram_family_transf_whisker_path B WalkingArrow_cat C C1 D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@eq_trans _ _ _ _ (@one_cat_zero_composite_prewhisker_path B (Functor_cat
  WalkingArrow_cat C) C C1 t T T0 D (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)
  (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@cokernel_adjunction_projection C S t T0 Q) (@one_cat_cokernel_whole_annihilation C S C1 t T T0 Q))
  (@one_cat_cokernel_family_zero_view_path B C S C1 t T T0 Q D)));
