/* Whole native kernel projection and its original-inclusion observations.
   Γ is source evaluation after the existing inverse mate. Its native
   endpoints remain inside compositions/applications; raw views are paths.
   Whiskering and generic functoriality derive the original κ_D equation. */
require open emdash.emdash3_2_one_cat_kernel_family_restriction_paths;
require open emdash.emdash3_2_one_cat_whiskering_paths;

// Source evaluation commutes with restriction of the original counit.
symbol one_cat_kernel_family_counit_source_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat
    WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
    (@kernel_adjunction_func C S t T P)) D) D (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C)
    (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func
    (Functor_cat WalkingArrow_cat C))) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)))
    walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
    (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
    (@kernel_adjunction_inclusion C S t T P)))
≔ @one_cat_whiskering_path (Functor_cat WalkingArrow_cat C) B (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat
  C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P));

// Its existing raw-whiskering observation preserves the same original inclusion.
symbol one_cat_kernel_family_inclusion_whisker_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (D : τ (Functor B
    (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@kernel_adjunction_family_inclusion_transf B C S t
    T P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t
    T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T
    P)))
≔ @one_cat_diagram_family_transf_reindex_path B (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1
    (@kernel_adjunction_arrow_func C S t T P) D walking_arrow_src walking_arrow_tgt walking_arrow_generator;

// First-class Γ_D: source evaluation after the whole inverse mate.
symbol one_cat_kernel_family_projection_func [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (Functor (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D)))
≔ @comp_cat_fapp0 (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  X) D) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))
    (@fapp1_func (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
      WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D)
      (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P) X D);

// Applying that whole functor retains the original native inverse and parent data.
symbol one_cat_kernel_family_projection_beta [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (v : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
  : τ (@= (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))) (@fapp0 (Hom_cat (Functor_cat B
    C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
    walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func
    B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src)
    D)) (@one_cat_kernel_family_projection_func B C S C1 t T P X D) v) (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src))
≔ @eq_refl (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D (@fapp0 _ _
  (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src);

// Γ_D(v)=κ_D∘v, first at the original raw-whiskered inclusion.
symbol one_cat_kernel_family_projection_raw_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (v : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) X
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
    (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)) v))
≔ let ep : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func
  C S t T P) D)) D) ≔ (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) D (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat
  C))) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P))) in
  let ja : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P) D))) ≔ (@fapp0 _ _ (@comp_cat_cov_fapp1_func B C (Functor_cat WalkingArrow_cat
    C) (@terminal_arrow_diagram_func C t T) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P) D)) v) in
  let ep0 : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
    D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) ≔ (@sym_transf_tapp0_transf B
    WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) D ep
    walking_arrow_src) in
  let ja0 : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
    D)) ≔ (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P) D)) ja walking_arrow_src) in
  @eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
    (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X
    D) v) walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@comp_fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) D ep ja) walking_arrow_src)
    (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@fapp0 _ _
    (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)) v)
    (@eq_ap (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) X) D) (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src))
      (λ h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) X) D), (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B
        C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D h walking_arrow_src))
      (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
        (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X D) v) (@comp_fapp0 (Functor_cat
        B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) X) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P) D)) D ep ja)
      (@one_cat_adjunction_family_untranspose_agrees B C (Functor_cat WalkingArrow_cat C)
        C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
          (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P) X D v))
    (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) X) D (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) (@comp_cat_fapp0 B
      C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat
      WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) D ep ja) walking_arrow_src) (@comp_fapp0
      (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) ep0 ja0) (@comp_fapp0 (Functor_cat B C) X
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
      (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
      WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)) v)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) (@comp_cat_fapp0
          B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat
          WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) D ep ja)
      (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
        (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) ep0 ja0) (@comp_fapp0 (Functor_cat B C)
        X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
        (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)) ja0) (@comp_fapp0
        (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
        (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)) v)
        (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
          D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C X
          (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
          (λ e : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T
            P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
            X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
            (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) e ja0)) ep0 (@fapp0 _ _
            (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P)
            (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T
            P))
          (@one_cat_kernel_family_counit_source_path B C S C1 t T P D))
        (@eq_ap (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T
          P) D)) (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
          (λ a : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t
            T P) D)), (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
            (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
            (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S
            t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C
            S t T P)) a)) ja0 v
          (@terminal_arrow_family_action_source_path B C t T X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
            (@kernel_adjunction_func C S t T P) D) v))));

// Use the existing graph presentation of the same original inclusion.
symbol one_cat_kernel_family_projection_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (v : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) X
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t
    T P D) v))
≔ @eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat
  WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src) (@comp_fapp0
  (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)) v) (@comp_fapp0 (Functor_cat B C) X
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T
  P D) v)
    (@one_cat_kernel_family_projection_raw_path B C S C1 t T P X D v)
    (@eq_sym (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
      (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S
      t T P D) v) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P)) v)
      (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C X (@diagram_family_at_func
        B WalkingArrow_cat C D walking_arrow_src))
        (λ k : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T
          P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) X
          (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
          (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) k v))
          (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
          WalkingArrow_cat C) C D (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
          walking_arrow_src)) (@kernel_adjunction_inclusion C S t T P))
        (@one_cat_kernel_family_inclusion_whisker_path B C S C1 t T P D)));

// The first-class Γ functor has this same original-inclusion observation.
symbol one_cat_kernel_family_projection_functor_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (v : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@fapp0 (Hom_cat
    (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func
    B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B C) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
    WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X)) (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
    WalkingArrow_cat C walking_arrow_src) D)) (@one_cat_kernel_family_projection_func B C S C1 t T P X D) v)
    (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@kernel_adjunction_family_inclusion_transf B C S t T P D) v))
≔ @eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@fapp0 (Hom_cat
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B C) (@fapp0
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
  WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X)) (@fapp0
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
  WalkingArrow_cat C walking_arrow_src) D)) (@one_cat_kernel_family_projection_func B C S C1 t T P X D) v)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat
  WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src) (@comp_fapp0
  (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T
  P D) v)
    (@one_cat_kernel_family_projection_beta B C S C1 t T P X D v)
    (@one_cat_kernel_family_projection_path B C S C1 t T P X D v);
