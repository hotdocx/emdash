/* The actual whole image-to-kernel comparison and its retained native factorization. */
require open emdash.emdash3_2_one_cat_image_kernel_comparison;

// The constructed comparison has its original image and kernel endpoints.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D));

// Native inverse mating of coimage descent recovers its complete input.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) ≡ (@one_cat_cokernel_family_input B C C1 t T T0
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
    (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
    (@one_cat_boundary_kills_incoming_kernel_path B C S C1 t T T0 P A D h));

// Native cancellation cannot replace that input by an unrelated one.
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (other : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
    (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B C
    (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D))))
  ⊢ (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    D)) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) ≡ other;

// Whole reconstruction through the same a_F.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ (@one_cat_image_kernel_reconstruction_path B C S C1 t T T0 P Q A D h N) : τ (@= (@Transf B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h));

// The native inverse-mate observation recovers the original H boundary.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ @one_cat_image_kernel_native_reconstruction_path B C S C1 t T T0 P Q A D h N : τ (@= (@Transf B C A (@fapp0
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
    (@kernel_adjunction_arrow_func C S t T P) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B C
    (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
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
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h));

// Reconstruction determines the whole comparison uniquely.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (b : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D))) (p : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b (@fapp0 _ _
    (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h)
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D
    h)))
  ⊢ @one_cat_image_kernel_unique B C S C1 t T T0 P Q A D h N b p : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D)) b (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N));

// The component keeps Im at the original incoming diagram and K at D(b).
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C)
    C (@adjunction_image_func C S t T T0 P Q) (@fapp0 B (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_family_incoming_func B C t T A D h) b)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)));

// Whole reconstruction retains the complete off-diagonal Hom functor.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (b c : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (Functor
    (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) c))) (λ z : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D)), (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
    C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b c z)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@one_cat_image_kernel_reconstruction_path B C S C1
    t T T0 P Q A D h N) : τ (@= (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) c))) (@tapp1_func B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) (@tapp1_func B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)));

// Whole reconstruction retains an arbitrary original base arrow.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (b c : τ (Obj B)) (p : τ (Hom B b c))
  ⊢ @eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (Hom C
    (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
    c)) (λ z : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T
    T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)),
    (@tapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c z p))
    (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S
    t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
    C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
    (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t
    T A D h) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D
    h) (@one_cat_image_kernel_reconstruction_path B C S C1 t T T0 P Q A D h N) : τ (@= (Hom C (@fapp0 B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
    c)) (@tapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c
    (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S
    t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
    C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
    (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t
    T A D h) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) p) (@tapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b c (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)
    p));

// Whole reconstruction retains the next Hom functor with retained endpoints.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (b c : τ (Obj B)) (p q : τ (Hom B b c))
  ⊢ @eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)) (Obj
    (@LaxArrow_cat Cat_cat)) (λ z : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D)), (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) p q) (Hom_cat
    (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0
    P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P
    D) c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b c z) p) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
    c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c z) q))
    (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b c z) p q))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h) (@one_cat_image_kernel_reconstruction_path B C S C1
    t T T0 P Q A D h N) : τ (@= (Obj (@LaxArrow_cat Cat_cat)) (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) p q)
    (Hom_cat (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
    S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C
    S t T P D) c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
    C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b c (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) p) (@fapp0
    (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b c (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) q)) (@fapp1_func
    (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) b c (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
    WalkingArrow_cat C) C (@zero_arrow_family_incoming_func B C t T A D h) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))) p q)) (@lax_edge
    Cat_cat (Hom_cat (Hom_cat B b c) p q) (Hom_cat (Hom_cat C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
    c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) p) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
    c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) q)) (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0
    B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
    c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
    Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D) b c
    (@one_cat_coimage_to_kernel_transf B C S C1 t T T0 P Q A D h)) p q)));
