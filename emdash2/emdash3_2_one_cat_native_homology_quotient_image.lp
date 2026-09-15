/* Original image and kernel comparisons for the cycle projection. */
require open emdash.emdash3_2_one_cat_native_homology_quotient_comparison;
require open emdash.emdash3_2_one_cat_image_family_covers;

// The original image kernel lies in the original g-cycles, using ḡ∘π_f=g.
symbol one_cat_native_homology_quotient_image_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) D) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K
  C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))) B D g
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K
  C A B f)))) (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))) D))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C B D) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))) D) (λ v : τ (@Transf K
  C B D), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@transf_arrow_diagram_func K C A B f))) B D v (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))))) _ _ (@eq_sym _ _ _
  (@one_cat_native_homology_quotient_outgoing_reconstruction K C S C1 t T T0 P Q A B D f g z))) (@eq_trans _ _
  _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K
  C A B f))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))) D)
  (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z) v)) _ _
  (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat
  C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func
  K C A B f)))) (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T
  P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))));

// The original whole K(g) mate maps Im(f) into the original cycles.
symbol one_cat_native_homology_quotient_image_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0
  K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@transf_arrow_diagram_func K C A B f))) (@transf_arrow_diagram_func K C B D g)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K
  C A B f))) (@one_cat_native_homology_quotient_image_zero K C S C1 t T T0 P Q A B D f g z));

// The original cycle inclusion reconstructs the image lift.
symbol one_cat_native_homology_quotient_image_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) B) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K
  C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_native_homology_quotient_image_lift K C S C1 t T T0 P Q A B D f g z))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K
  C A B f))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S
  t
  T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@transf_arrow_diagram_func K C B D g) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@one_cat_native_homology_quotient_image_zero K C S C1 t T T0 P Q A B D f g z));

// Original inclusion cancellation identifies the image-source factor with the original β.
symbol one_cat_native_homology_quotient_image_boundary_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)))
  (@comp_fapp0 (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@one_cat_native_homology_quotient_image_lift K C S C1 t T T0 P Q A
  B D f g z) (@one_cat_image_family_source_transf K C S C1 t T T0 P Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_boundary_transf K C S t T P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z)))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P A (@transf_arrow_diagram_func K C B D g)
  (@comp_fapp0 (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@one_cat_native_homology_quotient_image_lift K C S C1 t T T0 P Q A
  B D f g z) (@one_cat_image_family_source_transf K C S C1 t T T0 P Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_boundary_transf K C S t T P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@eq_trans _ _ _
  _ (@comp_assoc (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@transf_arrow_diagram_func K C A B f))) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) B (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@one_cat_native_homology_quotient_image_lift K C S C1 t T T0 P Q A
  B D f g z) (@one_cat_image_family_source_transf K C S C1 t T T0 P Q (@transf_arrow_diagram_func K C A B f)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@transf_arrow_diagram_func K C A B f))) B) (@Transf K C A B) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  B), (@comp_fapp0 (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@transf_arrow_diagram_func K C A B f))) B v (@one_cat_image_family_source_transf K C S C1 t T T0 P Q
  (@transf_arrow_diagram_func K C A B f)))) _ _ (@one_cat_native_homology_quotient_image_reconstruction K C S
  C1 t T T0 P Q A B D f g z)) (@eq_trans _ _ _ _ (@one_cat_image_family_source_factor_path K C S C1 t T T0 P Q
  (@transf_arrow_diagram_func K C A B f)) (@eq_sym _ _ _
  (@one_cat_native_homology_quotient_boundary_reconstruction K C S C1 t T T0 P Q A B D f g z))))));

// The original K(ρ) inclusion maps into the kernel of the original π_f.
symbol one_cat_native_homology_quotient_kernel_image_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))))
  (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (λ v : τ (@Transf K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))))) _ _ (@eq_sym _ _ _
  (@one_cat_native_homology_quotient_projection_reconstruction K C S C1 t T T0 P Q A B D f g z))) (@eq_trans _
  _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (λ v : τ (@Transf K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))), (@comp_fapp0 (Functor_cat K
  C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))) v)) _ _
  (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))))
  (@one_cat_zero_family_postcompose_path K C C1 t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))))))));

// The original image kernel receives the ambient K(ρ) map.
symbol one_cat_native_homology_quotient_kernel_image_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@transf_arrow_diagram_func K C A B f)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))))
  (@one_cat_native_homology_quotient_kernel_image_zero K C S C1 t T T0 P Q A B D f g z));

// The original image inclusion reconstructs that K(ρ) lift.
symbol one_cat_native_homology_quotient_kernel_image_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory
  C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))) B) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K
  C A B f))) (@one_cat_native_homology_quotient_kernel_image_lift K C S C1 t T T0 P Q A B D f g z))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S
  t
  T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func
  K C B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@transf_arrow_diagram_func K C A B f)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K
  C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))))
  (@one_cat_native_homology_quotient_kernel_image_zero K C S C1 t T T0 P Q A B D f g z));

// Original cycle inclusion cancellation gives v∘j=κ_ρ.
symbol one_cat_native_homology_quotient_kernel_cycle_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_native_homology_quotient_image_lift K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_kernel_image_lift K C S C1 t T T0 P Q A B D f g z))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))) (@transf_arrow_diagram_func
  K C B D g) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_native_homology_quotient_image_lift K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_kernel_image_lift K C S C1 t T T0 P Q A B D f g z))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_native_homology_quotient_image_lift K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_kernel_image_lift K C S C1 t T T0 P Q A B D f g z)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) B) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z))) B) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  B), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@transf_arrow_diagram_func K C A B f))) B
  v (@one_cat_native_homology_quotient_kernel_image_lift K C S C1 t T T0 P Q A B D f g z))) _ _
  (@one_cat_native_homology_quotient_image_reconstruction K C S C1 t T T0 P Q A B D f g z))
  (@one_cat_native_homology_quotient_kernel_image_reconstruction K C S C1 t T T0 P Q A B D f g z))));
