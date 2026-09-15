/* Original kernel-precomposition cover source maps into the original cycles. */
require open emdash.emdash3_2_one_cat_native_homology_quotient_comparison;
require open emdash.emdash3_2_one_cat_kernel_precomposition;

// The original precomposition-kernel inclusion is also a g-cycle.
symbol one_cat_native_homology_quotient_cover_source_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) D)
  (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) B D g
  (@kernel_precomposition_first_transf K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))))
  (@zero_arrow_family_zero_transf K C t T T0 (@kernel_precomposition_family_func K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) D))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C B D) (@Transf K C (@kernel_precomposition_family_func K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) D) (λ v
  : τ (@Transf K C B D), (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) B D v
  (@kernel_precomposition_first_transf K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))))) _ _
  (@eq_sym _ _ _ (@one_cat_native_homology_quotient_outgoing_reconstruction K C S C1 t T T0 P Q A B D f g z)))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C S t
  T P B (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A
  B D f g z)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B
  f))) B (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_precomposition_first_transf K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))))
  (@one_cat_kernel_precomposition_projection_zero_path K C S C1 t T T0 P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))));

// The original K(g) mate receives the native precomposition cover source.
symbol one_cat_native_homology_quotient_cover_source_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@Transf K C (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_precomposition_family_func K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@transf_arrow_diagram_func K C B D g) (@kernel_precomposition_first_transf K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@one_cat_native_homology_quotient_cover_source_zero K C S C1 t T T0 P Q A B D f g z));

// The original cycle inclusion reconstructs that cover-source lift.
symbol one_cat_native_homology_quotient_cover_source_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory
  C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) B)
  (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_native_homology_quotient_cover_source_lift K C S C1 t T T0 P Q A B D f g z))
  (@kernel_precomposition_first_transf K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_precomposition_family_func K
  C
  S t T P B (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A
  B D f g z)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B
  f))) (@transf_arrow_diagram_func K C B D g) (@kernel_precomposition_first_transf K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@one_cat_native_homology_quotient_cover_source_zero K C S C1 t T T0 P Q A B D f g z));

// Original inclusion cancellation proves ρ∘u equals the existing kernel-precomposition cover.
symbol one_cat_native_homology_quotient_cover_projection_reconstruction [K C : Cat] [S : τ
  (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))) (@comp_fapp0 (Functor_cat K
  C) (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_cover_source_lift K C S C1 t T T0 P Q A B D f g z))
  (@one_cat_kernel_precomposition_second_transf K C S C1 t T T0 P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P (@kernel_precomposition_family_func K C S t
  T
  P B (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A
  B D f g z)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B
  f))) (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A
  B D f g z)) (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_cover_source_lift K C S C1 t T T0 P Q A B D f g z))
  (@one_cat_kernel_precomposition_second_transf K C S C1 t T T0 P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_cover_source_lift K C S C1 t T T0 P Q A B D f g z)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (@Transf K C
  (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (λ v : τ (@Transf K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))), (@comp_fapp0
  (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) v
  (@one_cat_native_homology_quotient_cover_source_lift K C S C1 t T T0 P Q A B D f g z))) _ _
  (@one_cat_native_homology_quotient_projection_reconstruction K C S C1 t T T0 P Q A B D f g z)) (@eq_trans _
  _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_native_homology_quotient_cover_source_lift K C S C1 t T T0 P Q A B D f g z))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) B)
  (@Transf K C (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (λ v : τ (@Transf K
  C (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) B),
  (@comp_fapp0 (Functor_cat K C) (@kernel_precomposition_family_func K C S t T P B (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) v)) _ _
  (@one_cat_native_homology_quotient_cover_source_reconstruction K C S C1 t T T0 P Q A B D f g z)) (@eq_sym _
  _ _ (@one_cat_kernel_precomposition_square_path K C S C1 t T T0 P B (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f)))))))));
