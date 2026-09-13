/* Whole restricted kernel annihilation and the original H boundary.
   Preserve the actual boundary β=K(h)∘η. Native reconstruction, precomposition,
   zero and projection faithfulness derive its annihilation against K(f).
   All proofs concern whole transformations; no per-object cone data is input. */
require open emdash.emdash3_2_one_cat_zero_family_paths;
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_paths;
require open emdash.emdash3_2_image_coimage_adjunction_families;
require open emdash.emdash3_2_homology_adjunction_families;
require open emdash.emdash3_2_zero_arrow_family_observations;

// Initial-family uniqueness aligns the two qualified whole target presentations.
symbol one_cat_kernel_family_zero_view_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@zero_arrow_family_zero_transf B C t T T0
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) D))
    (@zero_arrow_family_zero_transf B C t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))
≔ @eq_ap (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@Transf
  B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (λ i : τ (@Transf B C (@Const_func B C t)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)), @comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@Const_func B C t)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) i (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) D)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_initial_family_arrow_path
  B C C1 t T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) D)) walking_arrow_src walking_arrow_tgt walking_arrow_generator));

// The original counit annihilation at an arbitrary original diagram family.
symbol one_cat_kernel_family_annihilation_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
    walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))
≔ @eq_trans (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P))) (@zero_arrow_family_zero_transf B C t T T0
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@eq_ap (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (λ k : τ
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) k))
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
  (@kernel_adjunction_inclusion C S t T P)) (@one_cat_diagram_family_transf_reindex_path B (Functor_cat
  WalkingArrow_cat C) WalkingArrow_cat C C1 (@kernel_adjunction_arrow_func C S t T P) D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)) (@eq_trans (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t
  T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C)
  C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
  (@kernel_adjunction_inclusion C S t T P))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@diagram_evaluation_transf
  WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)))
  (@zero_arrow_family_zero_transf B C t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@eq_ap
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (λ u : τ
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) u (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P))))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@fapp0
  _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@diagram_evaluation_transf
  WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@one_cat_diagram_family_transf_whisker_path B WalkingArrow_cat C C1 D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@eq_trans (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t
  T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
  (@kernel_adjunction_inclusion C S t T P))) (@zero_arrow_family_zero_transf B C t T T0 (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) D))
  (@zero_arrow_family_zero_transf B C t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@one_cat_zero_composite_prewhisker_path B (Functor_cat WalkingArrow_cat C) C C1 t T T0 D (@kernel_adjunction_func C
  S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) (@kernel_adjunction_inclusion C S t T P) (@diagram_evaluation_transf
  WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_kernel_whole_annihilation
  C S C1 t T T0 P)) (@one_cat_kernel_family_zero_view_path B C S C1 t T T0 P D)));

// Native inverse mating reconstructs the existing whole H boundary input.
symbol one_cat_kernel_family_boundary_projection_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@= (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) A D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
    walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D h))
≔ @eq_ap (@Transf B (Functor_cat WalkingArrow_cat C) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  A) D) (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ z : τ (@Transf B
  (Functor_cat WalkingArrow_cat C) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D),
  @sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
  C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D z
  walking_arrow_src) (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P) A D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) h
  (@one_cat_adjunction_family_transpose_reconstruction B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P) A D h);

// Projected annihilation implies kernel-valued annihilation by whole faithfulness.
symbol one_cat_kernel_family_projected_annihilation_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A0 A1 : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (a : τ (@Transf B C A0 A1))
  (h : τ (@Transf B C A1 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)))
  (p : τ (@= (@Transf B C A0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
    (Functor_cat B C) A0 A1 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) A1) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P) A1 D) h) walking_arrow_src) a) (@zero_arrow_family_zero_transf B
    C t T T0 A0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))))
  : τ (@= (@Transf B C A0 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (@comp_fapp0
    (Functor_cat B C) A0 A1 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D) h a)
    (@zero_arrow_family_zero_transf B C t T T0 A0 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)))
≔ @one_cat_kernel_family_projection_reflect_path B C S C1 t T T0 P A0 D (@comp_fapp0 (Functor_cat B C) A0 A1 (@fapp0
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D) h a) (@zero_arrow_family_zero_transf B C t T T0 A0
  (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (@eq_trans (@Transf B C A0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C)
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) A0) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func
  C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A0 D) (@comp_fapp0 (Functor_cat B
  C) A0 A1 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D) h a)) walking_arrow_src) (@comp_fapp0
  (Functor_cat B C) A0 A1 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func
  B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _
  (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) A1 D) h) walking_arrow_src) a) (@sym_transf_tapp0_transf B WalkingArrow_cat
  C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) D (@fapp0 _ _
  (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) A0 D) (@zero_arrow_family_zero_transf B C t T T0 A0 (@fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D))) walking_arrow_src) (@one_cat_kernel_family_projection_precomp_path B C S
  C1 t T P A0 A1 D a h) (@eq_trans (@Transf B C A0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) A0 A1 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  A1) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P) A1 D) h) walking_arrow_src) a) (@zero_arrow_family_zero_transf B C t
  T T0 A0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) D (@fapp0 _ _
  (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) A0 D) (@zero_arrow_family_zero_transf B C t T T0 A0 (@fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D))) walking_arrow_src) p (@eq_sym (@Transf B C A0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C)
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) A0) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func
  C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A0 D)
  (@zero_arrow_family_zero_transf B C t T T0 A0 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)))
  walking_arrow_src) (@zero_arrow_family_zero_transf B C t T T0 A0 (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@one_cat_kernel_family_projection_zero_path B C S C1 t T T0 P A0 D))));

// The actual β kills the original incoming kernel; no extra caller zero proof.
symbol one_cat_boundary_kills_incoming_kernel_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func
    C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) A (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
    (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
    walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)))
≔ @one_cat_kernel_family_projected_annihilation_path B C S C1 t T T0 P (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) A D
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@kernel_adjunction_family_boundary_transf B C S t T P
  A D h) (@eq_trans (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t
  T P) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) A (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C)
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) A) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat
  WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) walking_arrow_src) (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) A
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D
  h) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@zero_arrow_family_zero_transf B C t T T0
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@eq_ap (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (λ u : τ (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)),
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t
  T P) (@zero_arrow_family_incoming_func B C t T A D h)) A (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) u (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C
  t T A D h)) walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D (@fapp0 _ _
  (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) A D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
  walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D h)
  (@one_cat_kernel_family_boundary_projection_path B C S C1 t T P A D h)) (@one_cat_kernel_family_annihilation_path B
  C S C1 t T T0 P (@zero_arrow_family_incoming_func B C t T A D h)));
