/* Whole lift into the original source of a short-exact row.
   The existing K mate and original β inverse retain the entire Hom action. */
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;
require open emdash.emdash3_2_one_cat_functor_postcomposition_paths;
require open emdash.emdash3_2_eq1_evidence_property;

// The original row inverse reconstructs the original kernel inclusion.
symbol one_cat_short_exact_kernel_inverse_incoming_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) A
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D
    h) (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R))
    (@kernel_adjunction_family_inclusion_transf B C S t T P D))
≔ (@eq_trans (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) A
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D
  h) (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@one_cat_short_exact_family_kernel_inverse B C S C1
  t T T0 P Q A D h R)) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@eq_ap (@Transf B C A
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B C
  S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ u : τ (@Transf B C A
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  u (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R))) (@zero_arrow_family_incoming_transf B C
  t T A D h) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@eq_sym (@Transf B C A (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T
  P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf
  B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@zero_arrow_family_incoming_transf B
  C t T A D h) (@one_cat_row_kernel_reconstruction_path B C S C1 t T P A D h))) (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P D)) (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (λ u : τ (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P
  D)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B
  C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) u)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_inverse B C S C1 t
  T T0 P Q A D h R)) (@id (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D))
  (@omega_equiv_left_as_right_law (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T
  T0 P Q A D h R))));

// Native inverse-β postcomposition after the original whole K transpose.
symbol one_cat_short_exact_family_lift_func [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C))
  : τ (Functor (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat (Functor_cat B C) X A))
≔ @comp_cat_fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B C) X A)
    (@hom_postcomp_func (Functor_cat B C) (Functor_cat B C) (@id_func (Functor_cat B C)) X
      (@kernel_adjunction_family_func B C S t T P D) A (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q
      A D h R)) (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1
      (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
      C S t T P) (@kernel_adjunction_evidence C S t T P) X D);

// Its original-diagram input is the existing whole kernel input constructor.
symbol one_cat_short_exact_family_lift [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (k : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (z : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@Transf B C X A)
≔ @fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat (Functor_cat B C) X A)
  (@one_cat_short_exact_family_lift_func B C S C1 t T T0 P Q A D h R X) (@one_cat_kernel_family_input B C C1 t T
  T0 X D k z);

// Native application agrees with β⁻¹∘lift_K on the same original input.
symbol one_cat_short_exact_family_lift_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (k : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (z : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C X A) (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h R X k z) (@comp_fapp0
    (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D) A (@one_cat_short_exact_family_kernel_inverse B
    C S C1 t T T0 P Q A D h R) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)))
≔ @eq_refl (@Transf B C X A) (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h R X k z);

// The original incoming row map recovers the original whole k.
symbol one_cat_short_exact_family_lift_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (k : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (z : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat
    B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B
    C t T A D h) (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h R X k z)) k)
≔ (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
  (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T A D h) (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h
  R X k z)) (@comp_fapp0 (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T A D h) (@comp_fapp0 (Functor_cat B C) X (@kernel_adjunction_family_func
  B C S t T P D) A (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R)
  (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))) k (@eq_ap (@Transf B C X A) (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ u : τ (@Transf B C X A), (@comp_fapp0
  (Functor_cat B C) X A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T A D h) u)) (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A
  D h R X k z) (@comp_fapp0 (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D) A
  (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R) (@one_cat_kernel_family_lift B C S C1 t T
  T0 P X D k z)) (@one_cat_short_exact_family_lift_path B C S C1 t T T0 P Q A D h R X k z)) (@eq_trans (@Transf
  B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X A
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D
  h) (@comp_fapp0 (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D) A
  (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R) (@one_cat_kernel_family_lift B C S C1 t T
  T0 P X D k z))) (@comp_fapp0 (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S
  t T P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) k (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ u : τ (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)),
  (@comp_fapp0 (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) u (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) A (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D h) (@one_cat_short_exact_family_kernel_inverse B
  C S C1 t T T0 P Q A D h R)) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@one_cat_short_exact_kernel_inverse_incoming_path B C S C1 t T T0 P Q A D h R))
  (@one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P X D k z)));
