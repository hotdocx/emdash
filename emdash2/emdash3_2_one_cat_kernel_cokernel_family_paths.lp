/* Native whole kernel/cokernel inverse-mate observations.
   Faithfulness, annihilation and compatibility are derived from the original
   whole adjunctions and the ordinary family presentations. Original K/Q
   selections remain fixed; no ordinary factor record drives these operations. */
require open emdash.emdash3_2_one_cat_diagram_family_paths;
require open emdash.emdash3_2_kernel_cokernel_adjunctions;
require open emdash.emdash3_2_one_cat_terminal_family_paths;
require open emdash.emdash3_2_zero_arrow_family_action_paths;
require open emdash.emdash3_2_adjunction_untranspose_naturality;
require open emdash.emdash3_2_one_cat_adjunction_families;

// Faithfulness of E₀ after the native whole kernel inverse mate.
symbol one_cat_kernel_family_projection_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k l : τ (@Transf B C A (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
    D))) (p : τ (@= (@Transf B C A (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_src))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
    (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A
    D) k) walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) A D) l) walking_arrow_src)))
  : τ (@= (@Transf B C A (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))
    k l)
≔ @eq_ap (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D) (@Transf B C A (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D)) (λ h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D), @fapp0 _ _
  (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) A D) h)
    (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
      (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
      C S t T P) (@kernel_adjunction_evidence C S t T P) A D) k) (@fapp0 _ _
      (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P) A D) l)
    (@one_cat_terminal_family_test_reflect_path B C C1 t T T0 A D (@fapp0 _ _
      (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P) A D) k) (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C
      (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
      A D) l) p);

// Faithfulness of E₁ after the native whole cokernel inverse mate.
symbol one_cat_cokernel_family_projection_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat
    WalkingArrow_cat C)))
  (k l : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P)
    D) A)) (p : τ (@= (@Transf B C (@sym_fapp0_func B WalkingArrow_cat C D walking_arrow_tgt) A)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) A) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 P)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 P) D A) k) walking_arrow_tgt)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) A) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 P)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 P) D A) l) walking_arrow_tgt)))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) D)
    A) k l)
≔ @eq_ap (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) A)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 P) D) A) (λ h : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0
  B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) A)), @fapp0 _ _
  (@one_cat_adjunction_family_untranspose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
  WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 P) D A) h)
    (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
      (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 P)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 P) D A) k) (@fapp0 _ _
      (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
      WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 P) D A) l)
    (@one_cat_initial_family_test_reflect_path B C C1 t T T0 A D (@fapp0 _ _
      (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
      WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 P) D A) k) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B
      (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
      (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t
      T0 P) D A) l) p);

// E₀ of the original counit is the selected whole kernel inclusion κ.
symbol one_cat_kernel_structural_evaluation_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat
    C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat
    C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
    (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) walking_arrow_src)
    (@kernel_adjunction_inclusion C S t T P))
≔ eq_refl (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P))
  walking_arrow_src);

// The original counit derives ∂∘κ=0 as one equality of whole transformations.
symbol one_cat_kernel_whole_annihilation [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C
    walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@kernel_adjunction_inclusion C S t T P))
    (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@Const_func
    (Functor_cat WalkingArrow_cat C) C t) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
    (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
    WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
    C t T) (@kernel_adjunction_func C S t T P)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
≔ @eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_transf
  WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@kernel_adjunction_inclusion C S t
  T P)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
  (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
  t T) (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P)) walking_arrow_src)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat
  C) C) (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_family_transf (Functor_cat
  WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf
  (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)) (@eq_sym (@Transf (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0
  (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P))
  walking_arrow_src)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T
  P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat
  C walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@kernel_adjunction_inclusion C S t T P))
      (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@Transf (Functor_cat WalkingArrow_cat C)
        C (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (λ k
        : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)), @comp_fapp0 (Functor_cat (Functor_cat
        WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
        (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) k)
        (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C
        (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)) walking_arrow_src) (@kernel_adjunction_inclusion C S t T P)
        (@one_cat_kernel_structural_evaluation_path C S C1 t T T0 P)))
    (@eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat
      WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
      (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
      WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
      (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C
      (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P)) walking_arrow_src)) (@comp_fapp0 (Functor_cat (Functor_cat
      WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@sym_transf_tapp0_transf (Functor_cat
      WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
      WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func
      (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T
      P)) walking_arrow_tgt) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) walking_arrow_src walking_arrow_tgt
      walking_arrow_generator)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func
      C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_tgt) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0
      (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt
      walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) walking_arrow_src walking_arrow_tgt
      walking_arrow_generator)) (@strict_component_naturality_path WalkingArrow_cat (Functor_cat (Functor_cat
      WalkingArrow_cat C) C)
      (@sym_func (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C)
        C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)))
        (@sym_func (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat WalkingArrow_cat C)))
      (@sym_func_func_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C
        (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)))
      walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C
        (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_tgt)) (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (λ k : τ (@Transf (Functor_cat
        WalkingArrow_cat C) C (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_tgt)), @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
        (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) k (@diagram_family_transf (Functor_cat
        WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P))
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C
        (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)) walking_arrow_tgt) (@diagram_family_transf (Functor_cat
        WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
        WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@one_cat_initial_family_arrow_path (Functor_cat WalkingArrow_cat C) C C1 t T0 (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_tgt) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C)
        WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat
        WalkingArrow_cat C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
        T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) walking_arrow_tgt))));

// E₁ of the original unit is the selected whole cokernel projection q.
symbol one_cat_cokernel_structural_evaluation_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat
    C) WalkingArrow_cat C (@id_func (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat
    C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P))
    (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_tgt)
    (@cokernel_adjunction_projection C S t T0 P))
≔ eq_refl (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_tgt);

// The original unit derives q∘∂=0 as one equality of whole transformations.
symbol one_cat_cokernel_whole_annihilation [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@cokernel_adjunction_func C S t T0 P)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat
    C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P) (@cokernel_adjunction_projection C S
    t T0 P) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
    walking_arrow_generator)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@Const_func (Functor_cat WalkingArrow_cat C) C
    t) (@cokernel_adjunction_func C S t T0 P) (@diagram_family_transf (Functor_cat WalkingArrow_cat C)
    WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
    C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator)))
≔ @eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@cokernel_adjunction_func C S t T0 P)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat
  C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P) (@cokernel_adjunction_projection C S t
  T0 P) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S
  t T0 P) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@Const_func (Functor_cat
  WalkingArrow_cat C) C t) (@cokernel_adjunction_func C S t T0 P) (@diagram_family_transf (Functor_cat
  WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat
  C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@eq_sym (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_func C S t T0 P)) (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P)
  (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P)
  (@cokernel_adjunction_projection C S t T0 P) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))
      (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P)) (@Transf (Functor_cat WalkingArrow_cat C) C
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_func C S t T0 P)) (λ
        k : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P)), @comp_fapp0 (Functor_cat (Functor_cat
        WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P) k
        (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
        (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
        (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_tgt) (@cokernel_adjunction_projection C S t T0 P)
        (@one_cat_cokernel_structural_evaluation_path C S C1 t T T0 P)))
    (@eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@cokernel_adjunction_func C S t T0 P)) (@comp_fapp0 (Functor_cat (Functor_cat
      WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P)
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat (Functor_cat
      WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@Const_func
      (Functor_cat WalkingArrow_cat C) C t) (@cokernel_adjunction_func C S t T0 P) (@diagram_family_transf
      (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
      (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P))
      walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@sym_transf_tapp0_transf (Functor_cat
      WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat
      WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t
      T0 P)) walking_arrow_src)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@Const_func (Functor_cat WalkingArrow_cat C)
      C t) (@cokernel_adjunction_func C S t T0 P) (@diagram_family_transf (Functor_cat WalkingArrow_cat C)
      WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) walking_arrow_src walking_arrow_tgt
      walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@eq_sym (@Transf (Functor_cat WalkingArrow_cat C)
      C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_func C S t T0 P))
      (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@cokernel_adjunction_func C S t T0 P)
      (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
      WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_func C S t T0 P)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_src)) (@comp_fapp0 (Functor_cat (Functor_cat
      WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 P)
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@strict_component_naturality_path
      WalkingArrow_cat (Functor_cat (Functor_cat WalkingArrow_cat C) C)
      (@sym_func (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat WalkingArrow_cat C)))
        (@sym_func (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat
        C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0
        P)))
      (@sym_func_func_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
        (@cokernel_adjunction_evidence C S t T0 P)))
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C)
        C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@Const_func (Functor_cat
        WalkingArrow_cat C) C t)) (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_func C S t T0 P)) (λ k : τ (@Transf (Functor_cat
        WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@Const_func
        (Functor_cat WalkingArrow_cat C) C t)), @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@Const_func (Functor_cat WalkingArrow_cat
        C) C t) (@cokernel_adjunction_func C S t T0 P) (@diagram_family_transf (Functor_cat WalkingArrow_cat C)
        WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) walking_arrow_src
        walking_arrow_tgt walking_arrow_generator) k)
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@id_func (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 P)) (@unit_adj_transf (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P) (@initial_arrow_diagram_func C t T0)
        (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_src) (@diagram_family_transf (Functor_cat
        WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@one_cat_terminal_family_arrow_path (Functor_cat WalkingArrow_cat C) C C1 t T (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_src) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C)
        WalkingArrow_cat C (@id_func (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat
        C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0
        P)) (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 P)
        (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 P)) walking_arrow_src))));

// Projected native kernel inverse mating preserves precomposition by a whole map.
symbol one_cat_kernel_family_projection_precomp_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A0 A1 : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (a : τ (@Transf B C A0 A1)) (h : τ (@Transf B C A1 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)))
  : τ (@= (@Transf B C A0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) A0) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
    C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat
    C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t
    T P)) A0 D) (@comp_fapp0 (Functor_cat B C) A0 A1 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)
    h a)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A0 A1 (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C)
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P)) A1 D) h) walking_arrow_src) a))
≔ @eq_trans (@Transf B C A0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  A0) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func
  C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) A0 D) (@comp_fapp0 (Functor_cat
  B C) A0 A1 (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D) h a)) walking_arrow_src)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  A0) D (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) A0) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _
  (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func
  B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat
  WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) A1 D) h) (@fapp1_fapp0 (Functor_cat B
  C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) A0 A1 a)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A0 A1
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _ (@adjunction_untranspose_func
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P)) A1 D) h) walking_arrow_src) a) (@eq_ap (@Transf B (Functor_cat
  WalkingArrow_cat C) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) D) (@Transf B C A0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ v : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) D), (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) D v walking_arrow_src))
      (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
        (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
        (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
        WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)) A0 D) (@comp_fapp0 (Functor_cat B C) A0 A1 (@fapp0 (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) D) h a)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C
        (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) (@fapp0 (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
        (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) A1 D) h) (@fapp1_fapp0
        (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0 A1 a)) (@eq_sym (@Transf B (Functor_cat
        WalkingArrow_cat C) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) D)
        (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) A0) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
        t T)) A1) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
        t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
        (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
        WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)) A1 D) h) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
        t T)) A0 A1 a)) (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
        t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
        (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
        WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)) A0 D) (@comp_fapp0 (Functor_cat B C) A0 A1 (@fapp0 (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) D) h a)) (@untranspose_precomp_path (Functor_cat B C) (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
        (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) A0 A1 D a h)))
    (@eq_trans (@Transf B C A0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
      T)) A0) D (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
      (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) A0) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
      C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0
      _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
      (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P)) A1 D) h) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
      T)) A0 A1 a)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A0 A1 (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C)
      (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C)
      (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
      (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
      C S t T P) (@kernel_adjunction_evidence C S t T P)) A1 D) h) walking_arrow_src) (@sym_transf_tapp0_transf B
      WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A0) (@fapp0
      (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
      WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B
      (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) A0 A1 a) walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) A0 A1
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat
      C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C
      (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _
      (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
      (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P)) A1 D) h) walking_arrow_src) a)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src (@fapp0 (Functor_cat B
      C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) A0) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
      C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0
      _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
      (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P)) A1 D) h) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
      T)) A0 A1 a)) (@eq_ap (@Transf B C A0 A1) (@Transf B C A0 (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src))
      (λ v : τ (@Transf B C A0 A1), @comp_fapp0 (Functor_cat B C) A0 A1 (@diagram_family_at_func B WalkingArrow_cat C
        D walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) A1) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
        (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) A1 D) h) walking_arrow_src) v)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
        t T)) A0) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C
        (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A1) (@fapp1_fapp0 (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) A0 A1 a) walking_arrow_src) a (@terminal_arrow_family_action_source_path
        B C t T A0 A1 a)));

// Projected native kernel inverse mating sends the whole canonical zero to zero.
symbol one_cat_kernel_family_projection_zero_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@= (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D (@fapp0 _ _
    (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func
    B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C
    (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P))
    A D) (@comp_fapp0 (Functor_cat B C) A (@Const_func B C t) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)
    (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
    walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src
    walking_arrow_tgt walking_arrow_generator))) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A (@Const_func B C
    t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator)))
≔ @eq_trans (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  A) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func
  C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) A D) (@comp_fapp0 (Functor_cat B
  C) A (@Const_func B C t) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A (@Const_func B C t)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@Const_func B C t)) D (@fapp0 _ _
  (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func
  B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat
  WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) (@Const_func B C t) D)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)) walking_arrow_src) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) A (@Const_func B C t)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@one_cat_kernel_family_projection_precomp_path B C S C1 t T P A (@Const_func B C t) D (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@eq_ap
  (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C A
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (λ v : τ (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)),
        @comp_fapp0 (Functor_cat B C) A (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) v (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src walking_arrow_tgt
        walking_arrow_generator))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
        t T)) (@Const_func B C t)) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
        (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) (@Const_func B C t) D)
        (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
        C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)) walking_arrow_src) (@diagram_family_transf B
        WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src walking_arrow_tgt
        walking_arrow_generator)
      (@one_cat_initial_family_arrow_path B C C1 t T0 (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C) (Functor_cat B
        (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@Const_func B C t)) D (@fapp0 _ _ (@adjunction_untranspose_func
        (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat
        C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C)
        C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) (@Const_func B C t) D)
        (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
        C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)) walking_arrow_src)));
