/* Cancellation of the actual incoming/outgoing maps of a whole short-exact row. */
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_omega_equiv_cancellation_paths;
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_short_exact_families;

// Original β reconstructs the original whole incoming row map.
symbol one_cat_row_kernel_reconstruction_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D))
  : τ (@= (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat
    B C) A (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@zero_arrow_family_incoming_transf B C t T A D h))
≔ (@eq_trans (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
  (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D (@fapp0 (Hom_cat (Functor_cat B C) A (@fapp0
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat
  C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D) (@one_cat_adjunction_family_untranspose_func B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func
  C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T A D h) (@eq_sym (@Transf B C A (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@fapp0 (Functor_cat B C)
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) A) D (@fapp0 (Hom_cat (Functor_cat B C) A (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D) (@one_cat_adjunction_family_untranspose_func B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func
  C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A
  D h)) (@one_cat_kernel_family_projection_path B C S C1 t T P A D (@kernel_adjunction_family_boundary_transf B C S t
  T P A D h))) (@one_cat_kernel_family_boundary_projection_path B C S C1 t T P A D h));

// Original γ reconstructs the original whole outgoing row map.
symbol one_cat_row_cokernel_ambient_reconstruction_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
    (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@zero_arrow_family_incoming_func B C t T A D
    h))) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @one_cat_cokernel_family_descent_ambient_reconstruction B C S C1 t T T0 Q (@zero_arrow_family_incoming_func B
  C t T A D h) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_zero_family_chain_path B C C1 t T T0 A D h);

// The original incoming whole map reflects equality by κ then β cancellation.
symbol one_cat_short_exact_family_incoming_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  (X : τ (Functor B C)) (u v : τ (@Transf B C X A))
  (p : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
    (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@zero_arrow_family_incoming_transf B C t T A D h) u) (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D h) v)))
  : τ (@= (@Transf B C X A) u v)
≔ @omega_equiv_postcomp_reflect_path (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T
  T0 P Q A D h R) X u v
    (@one_cat_kernel_family_inclusion_reflect_path B C S C1 t T T0 P X D
      (@comp_fapp0 (Functor_cat B C) X A (@kernel_adjunction_family_func B C S t T P D)
        (@kernel_adjunction_family_boundary_transf B C S t T P A D h) u) (@comp_fapp0 (Functor_cat B C) X A
        (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
        v)
      (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
        (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_fapp0
        (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat
        C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
        (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) u) (@comp_fapp0 (Functor_cat B C) X A
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T
        A D h) u) (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf
        B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) v) (@eq_ap (@Transf B C A
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C X (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src)) (λ j : τ (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C
        D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) j u)) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf
        B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
        (@zero_arrow_family_incoming_transf B C t T A D h) (@one_cat_row_kernel_reconstruction_path B C S C1 t T
        P A D h)) (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
        (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@zero_arrow_family_incoming_transf B C t T A D h) u) (@comp_fapp0 (Functor_cat B C) X A
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T
        A D h) v) (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf
        B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) v) p (@eq_ap (@Transf B C A
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C X (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src)) (λ j : τ (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C
        D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) j v)) (@zero_arrow_family_incoming_transf B C t T A D h) (@comp_fapp0 (Functor_cat B C) A
        (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
        (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@eq_sym (@Transf B C A
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) A
        (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
        (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@zero_arrow_family_incoming_transf B C t T A D
        h) (@one_cat_row_kernel_reconstruction_path B C S C1 t T P A D h))))));

// The outgoing whole map reflects equality by q then γ cancellation.
symbol one_cat_short_exact_family_outgoing_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  (Y : τ (Functor B C)) (u v : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (p : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0
    (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) Y u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y v
    (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) u v)
≔ @omega_equiv_precomp_reflect_path (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
  (@one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h R) Y u v
    (@one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q (@zero_arrow_family_incoming_func B C t T
      A D h) Y
      (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func
        C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_tgt) Y u (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)) (@comp_fapp0 (Functor_cat B
        C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
        (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_tgt) Y v (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h))
      (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func
        B WalkingArrow_cat C D walking_arrow_tgt) Y u (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
        (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1
        t T T0 Q A D h) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
        (@zero_arrow_family_incoming_func B C t T A D h)))) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
        (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y v (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1
        t T T0 Q A D h) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
        (@zero_arrow_family_incoming_func B C t T A D h)))) (@eq_ap (@Transf B C (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
        (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (λ j : τ (@Transf B C
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat
        C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u j)) (@comp_fapp0
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
        (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B
        C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
        (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
        (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@zero_arrow_family_incoming_func B C t T A
        D h))) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
        walking_arrow_generator) (@one_cat_row_cokernel_ambient_reconstruction_path B C S C1 t T T0 Q A D h))
        (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (@comp_fapp0
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func
        B WalkingArrow_cat C D walking_arrow_tgt) Y u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
        walking_arrow_tgt walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y v
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
        (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y v (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1
        t T T0 Q A D h) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
        (@zero_arrow_family_incoming_func B C t T A D h)))) p (@eq_ap (@Transf B C (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
        (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y) (λ j : τ (@Transf B C
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat
        C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y v j))
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
        (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
        (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@zero_arrow_family_incoming_func B C t T A
        D h))) (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
        WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1
        t T T0 Q A D h) (@cokernel_adjunction_family_projection_transf B C S t T0 Q
        (@zero_arrow_family_incoming_func B C t T A D h))) (@diagram_family_transf B WalkingArrow_cat C D
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@one_cat_row_cokernel_ambient_reconstruction_path B C S C1 t T T0 Q A D h))))));
