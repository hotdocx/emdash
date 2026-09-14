require open emdash.emdash3_2_one_cat_image_kernel_inclusion_paths;
require open emdash.emdash3_2_one_cat_inverse_from_universal_zeros;
require open emdash.emdash3_2_one_cat_homology_cover_maps;
require open emdash.emdash3_2_one_cat_short_exact_families;

// A derived zero boundary quotient forces the actual comparison cokernel projection to zero.
symbol one_cat_image_kernel_comparison_cokernel_zero [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (z : τ (@= (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h))
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h) (@zero_arrow_family_zero_transf B C t T
  T0 (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h))))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@cokernel_adjunction_family_func B C S t T0
  Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))) (@cokernel_adjunction_family_projection_transf
  B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C S t T P D)
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))))
≔ @one_cat_coimage_cover_reflect_path B C S C1 t T T0 P Q (@kernel_adjunction_family_boundary_diagram_func B C S t
  T P A D h) (@one_cat_zero_cokernel_cover_omega B C S C1 t T T0 P Q N
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) z) (@cokernel_adjunction_family_func B C S t
  T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C S t T P D)
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)) (@Transf B C A
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))))
  (λ v : τ (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)), (@comp_fapp0 (Functor_cat B C) A
  (@kernel_adjunction_family_func B C S t T P D) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@cokernel_adjunction_family_projection_transf B
  C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  v)) (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@comp_fapp0 (Functor_cat B C) A
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@cokernel_adjunction_family_projection_transf B C
  S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)))) (@eq_sym _ _ _
  (@one_cat_coimage_kernel_ambient_reconstruction B C S C1 t T T0 P Q A D h))) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat B C) A (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func
  C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N))) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C
  t T A D h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))))
  (@Transf B C A (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N)))) (λ v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))),
  (@comp_fapp0 (Functor_cat B C) A (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func
  C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) v (@cokernel_adjunction_family_projection_transf
  B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))))) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N))) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) (@zero_arrow_family_zero_transf B C t
  T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))) (λ v : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B
  C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B
  C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@cokernel_adjunction_family_projection_transf B
  C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  v)) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C
  t T A D h) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@eq_sym _ _ _
  (@one_cat_image_kernel_reconstruction_path B C S C1 t T T0 P Q A D h N))) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@cokernel_adjunction_family_projection_transf B
  C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C
  S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))))
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))) (λ v : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N)))), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N))) v (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N))) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)) (@zero_arrow_family_zero_transf B C t
  T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))) (@one_cat_cokernel_family_annihilation_path B C
  S C1 t T T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))))
  (@one_cat_zero_family_precompose_path B C C1 t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))))))) (@eq_trans
  _ _ _ _ (@one_cat_zero_family_precompose_path B C C1 t T T0 A (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@cokernel_adjunction_family_func B C S t T0 Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C
  t T A D h)))) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path B C C1 t T T0 A
  (@kernel_adjunction_family_func B C S t T P D) (@cokernel_adjunction_family_func B C S t T0 Q
  (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))) (@kernel_adjunction_family_boundary_transf B C S
  t T P A D h)))))));

// Original native K/Q and normality construct an inverse of the actual comparison from its boundary-zero criterion.
symbol one_cat_image_kernel_exact_from_boundary_zero [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (z : τ (@= (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h))
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h) (@zero_arrow_family_zero_transf B C t T
  T0 (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))
≔ @one_cat_zero_kernel_cokernel_omega B C S C1 t T T0 P Q (@transf_arrow_diagram_func B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q
  A D h N)) N (@one_cat_image_kernel_comparison_kernel_zero B C S C1 t T T0 P Q A D h N)
  (@one_cat_image_kernel_comparison_cokernel_zero B C S C1 t T T0 P Q A D h N z);

// The original short-exact row derives the boundary-zero premise through its fixed-forward comparison.
symbol one_cat_short_exact_boundary_quotient_zero [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ
  (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T
  T0 P Q A D h)) (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h)
  (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q A D h)))
≔ @omega_equiv_precomp_reflect_path (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1
  t T T0 P Q A D h R) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h) (@zero_arrow_family_zero_transf B C t T
  T0 (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h))
  (@eq_trans _ _ _ _ (@one_cat_cokernel_family_annihilation_path B C S C1 t T T0 Q
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path B C C1 t T T0 A (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q A D h) (@kernel_adjunction_family_boundary_transf B C S t T P
  A D h))));

// The actual image-to-kernel comparison of the original short-exact row is derived, not supplied as new evidence.
symbol one_cat_short_exact_image_kernel_omega [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (N : τ
  (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))
≔ @one_cat_image_kernel_exact_from_boundary_zero B C S C1 t T T0 P Q A D h N
  (@one_cat_short_exact_boundary_quotient_zero B C S C1 t T T0 P Q A D h R);
