require open emdash.emdash3_2_one_cat_cokernel_family_annihilation;
require open emdash.emdash3_2_one_cat_zero_family_postcomposition_paths;
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;
require open emdash.emdash3_2_one_cat_image_kernel_comparison;
require open emdash.emdash3_2_one_cat_coimage_cover_descent;
require open emdash.emdash3_2_one_cat_zero_cokernel_covers;
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_maps;

// The original coimage descent reconstructs the original whole boundary after its original quotient.
symbol one_cat_coimage_kernel_ambient_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A) D))
 : τ (@= (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0 (Functor_cat B C) A
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@cokernel_adjunction_family_projection_transf B C
  S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))))
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_cokernel_family_projection_path B C S C1 t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  D) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h))) (@one_cat_coimage_kernel_reconstruction_path
  B C S C1 t T T0 P Q A D h));

// Original quotient cancellation identifies the ambient coimage factor without changing any object.
symbol one_cat_coimage_kernel_inclusion_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_coimage_to_kernel_transf
  B C S C1 t T T0 P Q A D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)))
≔ @one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_coimage_to_kernel_transf
  B C S C1 t T T0 P Q A D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) A (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B
  C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_coimage_to_kernel_transf
  B C S C1 t T T0 P Q A D h) (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C A
  (@kernel_adjunction_family_func B C S t T P D)) (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (λ v : τ (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)), (@comp_fapp0
  (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) v)) (@comp_fapp0 (Functor_cat B
  C) A (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@cokernel_adjunction_family_projection_transf B C
  S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))))
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
  (@one_cat_coimage_kernel_ambient_reconstruction B C S C1 t T T0 P Q A D h)) (@eq_trans _ _ _ _
  (@one_cat_row_kernel_reconstruction_path B C S C1 t T P A D h) (@eq_sym _ _ _
  (@one_cat_coimage_family_factor_path B C S C1 t T T0 P Q (@zero_arrow_family_incoming_func B C t T A D h))))));

// The actual Im⇒K comparison retains the original image inclusion into the middle object.
symbol one_cat_image_kernel_ambient_inclusion_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_image_to_kernel_transf B
  C S C1 t T T0 P Q A D h N)) (@kernel_adjunction_family_inclusion_transf B C S t T P (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@zero_arrow_family_incoming_func B C t T A D h))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B
  C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_coimage_to_kernel_transf
  B C S C1 t T T0 P Q A D h) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ v : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B
  C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B
  C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) v (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S
  t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q
  N)))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_coimage_to_kernel_transf
  B C S C1 t T T0 P Q A D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)) (@one_cat_coimage_kernel_inclusion_path B C S C1 t T T0 P Q A D h)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0
  P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (λ v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) v (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S
  t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q
  N)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@zero_arrow_family_incoming_func
  B C t T A D h))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@eq_sym _ _ _
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D
  h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ v : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) v (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C
  S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))))
  (@kernel_adjunction_family_inclusion_transf B C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@zero_arrow_family_incoming_func
  B C t T A D h))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@adjunction_image_inclusion C S t T T0 P
  Q)) (@one_cat_image_family_kernel_path B C S C1 t T T0 P Q (@zero_arrow_family_incoming_func B C t T A D h)))
  (@one_cat_coimage_target_family_factor_path B C S C1 t T T0 P Q (@zero_arrow_family_incoming_func B C t T A D
  h))))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))))
  (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))) (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (λ v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h))), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@zero_arrow_family_incoming_func
  B C t T A D h))) v)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B
  C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
  (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h))) (@omega_equiv_left_as_right_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
  (@one_cat_adjunction_normality_family B C S C1 t T T0 P Q N (@zero_arrow_family_incoming_func B C t T A D
  h))))))));

// Original image-kernel cancellation proves the actual comparison has zero kernel inclusion.
symbol one_cat_image_kernel_comparison_kernel_zero [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B
  C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P
  Q A D h N))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h))) (@kernel_adjunction_family_inclusion_transf B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@zero_arrow_family_zero_transf B C t T T0
  (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h))))
≔ @one_cat_kernel_family_inclusion_reflect_path B C S C1 t T T0 P (@kernel_adjunction_family_func B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_inclusion_transf B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@zero_arrow_family_zero_transf B C t T T0
  (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@Transf B C
  (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ v : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) v (@kernel_adjunction_family_inclusion_transf B C S t T P (@transf_arrow_diagram_func B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))))) (@kernel_adjunction_family_inclusion_transf B
  C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)) (@eq_sym _ _ _
  (@one_cat_image_kernel_ambient_inclusion_path B C S C1 t T T0 P Q A D h N))) (@eq_trans _ _ _ _ (@eq_sym _
  _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_image_to_kernel_transf B
  C S C1 t T T0 P Q A D h N) (@kernel_adjunction_family_inclusion_transf B C S t T P (@transf_arrow_diagram_func B
  C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@kernel_adjunction_family_func B C S t T P D)) (@Transf B C (@kernel_adjunction_family_func B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@kernel_adjunction_family_func B C S t T P D)),
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@kernel_adjunction_family_func B C S t T P D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P D) v)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
  (@kernel_adjunction_family_inclusion_transf B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N)))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@kernel_adjunction_family_func B C S t T P D))
  (@one_cat_kernel_family_annihilation_path B C S C1 t T T0 P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N)))) (@eq_trans _ _ _ _ (@one_cat_zero_family_postcompose_path B C C1 t T T0
  (@kernel_adjunction_family_func B C S t T P (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@eq_sym _ _ _
  (@one_cat_zero_family_postcompose_path B C C1 t T T0 (@kernel_adjunction_family_func B C S t T P
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)))))))));
