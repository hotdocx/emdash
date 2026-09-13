/* Canonical whole Im(f)⇒K(g) in the ordinary Abelian setting.
   Descend the existing H boundary through Q at the original restricted
   kernel-arrow family, then use the same selected inverse of Coim⇒Im.
   Native reconstruction and uniqueness retain the original whole data. */
require open emdash.emdash3_2_one_cat_kernel_family_restriction_paths;
require open emdash.emdash3_2_one_cat_cokernel_family_descent;
require open emdash.emdash3_2_one_cat_adjunction_normality;

// Whole cokernel descent of β at the original restricted Arr(κ).
symbol one_cat_coimage_to_kernel_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D))
≔ @one_cat_cokernel_family_descent B C S C1 t T T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
  (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D) (@kernel_adjunction_family_boundary_transf B C S t T P
  A D h) (@one_cat_boundary_kills_incoming_kernel_path B C S C1 t T T0 P A D h);

// The same inverse of a, prewhiskered at the incoming family, gives Im(f)⇒K(g).
symbol one_cat_image_to_kernel_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D))
≔ @comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T
  T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@fapp0
  _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
  (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N));

// The constructed e satisfies e∘a_F=β̄ as one whole path.
symbol one_cat_image_kernel_reconstruction_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0
    (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
    (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t
    T A D h) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D
    h))
≔ @eq_trans (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0
  _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
  (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))))
  (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@eq_sym (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
  (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0
  _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@comp_assoc (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@fapp0
  _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
  (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) (@eq_ap (@Transf B
  C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))) (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (λ z : τ (@Transf
  B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))), (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) z))
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t
  T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C
  S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t
  T T0 P Q) (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@id
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h))) (@iso_evidence_left (Functor_cat B C) (@fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h)) (@adjunction_coimage_func C S t T T0 P Q)) (@fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h)) (@adjunction_image_func C S t T T0 P Q)) (@iso_evidence_fmap
  (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_iso_evidence C S C1 t T T0 P Q N))));

// Native inverse mating of β̄ recovers the original whole β.
symbol one_cat_coimage_kernel_reconstruction_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@= (@Transf B C A (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) walking_arrow_tgt)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
≔ @one_cat_cokernel_family_descent_reconstruction B C S C1 t T T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_boundary_kills_incoming_kernel_path B C S C1
  t T T0 P A D h);

// Native inverse mating of e∘a_F recovers that same whole β.
symbol one_cat_image_kernel_native_reconstruction_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  : τ (@= (@Transf B C A (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func
    C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
    C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
    (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t
    T A D h) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) walking_arrow_tgt)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
≔ @eq_trans (@Transf B C A (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
  WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t
  T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0
  _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) walking_arrow_tgt) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
  WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
  (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) walking_arrow_tgt)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D)) (@Transf B C A (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  D)) (λ b : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0
  P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)),
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
  WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
  b) walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T
  A D h)) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T
  A D h) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D
  h) (@one_cat_image_kernel_reconstruction_path B C S C1 t T T0 P Q A D h N))
  (@one_cat_coimage_kernel_reconstruction_path B C S C1 t T T0 P Q A D h);

// Reconstruction through a_F determines e uniquely among whole transformations.
symbol one_cat_image_kernel_unique [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  (b : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)))
  (p : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0
    (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) b
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N))
≔ @eq_trans (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) b (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) b (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))))
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@eq_sym (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T
  A D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func
  B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)))) b (@eq_ap
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))) (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (λ z : τ (@Transf
  B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))), (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) b z)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))) (@id
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h))) (@iso_evidence_right (Functor_cat B C) (@fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h)) (@adjunction_coimage_func C S t T T0 P Q)) (@fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C
  (@zero_arrow_family_incoming_func B C t T A D h)) (@adjunction_image_func C S t T T0 P Q)) (@iso_evidence_fmap
  (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_iso_evidence C S C1 t T T0 P Q N))))) (@eq_trans
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) b (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))))
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T
  T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_image_func C S t T T0 P Q)
  (@adjunction_coimage_func C S t T T0 P Q)) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)))
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@comp_assoc (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T
  A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) b (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
  (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))) (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D)) (λ q : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D)), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) q (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
  (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D
  h) p));
