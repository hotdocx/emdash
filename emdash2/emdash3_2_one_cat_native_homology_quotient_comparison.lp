/* Whole H=Q(β) comparison with the kernel of the original quotient differential.
   This first construction requires no native Abelian normality. */
require open emdash.emdash3_2_homology_adjunction_families;
require open emdash.emdash3_2_cokernel_adjunction_families;
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_cokernel_family_annihilation;
require open emdash.emdash3_2_one_cat_zero_family_postcomposition_paths;

// The original native boundary reconstructs κ_g∘β=f.
symbol one_cat_native_homology_quotient_boundary_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C A B) (@comp_fapp0 (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) B (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_boundary_transf K C S t T P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t T T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) f)
≔ (@eq_trans _ _ _ _ (@one_cat_row_kernel_reconstruction_path K C S C1 t T P A (@transf_arrow_diagram_func K C
  B
  D g) (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_kernel_family_input_source_path K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z));

// The original Q descent gives ḡ:Q(f)⇒D.
symbol one_cat_native_homology_quotient_outgoing [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@Transf K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D)
≔ (@one_cat_cokernel_family_descent K C S C1 t T T0 Q (@transf_arrow_diagram_func K C A B f) D g z);

// The original quotient reconstructs ḡ∘π_f=g.
symbol one_cat_native_homology_quotient_outgoing_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C B D) (@comp_fapp0 (Functor_cat K C) B (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A
  B D f g z) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B
  f))) g)
≔ (@one_cat_cokernel_family_descent_ambient_reconstruction K C S C1 t T T0 Q (@transf_arrow_diagram_func K C A
  B
  f) D g z);

// The original quotient sends cycles into K(ḡ).
symbol one_cat_native_homology_quotient_projection_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) D)
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
  D g)) (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))))
  (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) D))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) B (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A
  B D f g z) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B
  f)) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C B D) (@Transf K C (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) D) (λ v : τ (@Transf K C B D), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B D v
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g)))) _ _
  (@one_cat_native_homology_quotient_outgoing_reconstruction K C S C1 t T T0 P Q A B D f g z))
  (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@transf_arrow_diagram_func K C B D g))));

// ρ:K(g)⇒K(ḡ) is the original whole kernel mate of π_f∘κ_g.
symbol one_cat_native_homology_quotient_projection [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t
  T T0 P Q A B D f g z)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) B (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C B D g))) (@one_cat_native_homology_quotient_projection_zero K C S C1 t T T0
  P Q A B D f g z));

// The original kernel inclusion reconstructs κ_ḡ∘ρ=π_f∘κ_g.
symbol one_cat_native_homology_quotient_projection_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)) (@comp_fapp0 (Functor_cat K
  C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g))))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@kernel_adjunction_family_func K C S
  t
  T P (@transf_arrow_diagram_func K C B D g)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g)) B
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B D g)))
  (@one_cat_native_homology_quotient_projection_zero K C S C1 t T T0 P Q A B D f g z));

// Original inclusion cancellation proves ρ∘β=0.
symbol one_cat_native_homology_quotient_projection_boundary_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))) (@comp_fapp0 (Functor_cat K
  C) A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@kernel_adjunction_family_boundary_transf K C S t T P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z)))
  (@zero_arrow_family_zero_transf K C t T T0 A (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P A (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)) (@comp_fapp0 (Functor_cat K C)
  A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@kernel_adjunction_family_boundary_transf K C S t T P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z)))
  (@zero_arrow_family_zero_transf K C t T T0 A (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))) (@eq_trans _ _ _
  _ (@comp_assoc (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
  C B D g)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@kernel_adjunction_family_boundary_transf K C S t T P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (@Transf K C A
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (λ v : τ (@Transf K
  C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))), (@comp_fapp0
  (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) v
  (@kernel_adjunction_family_boundary_transf K C S t T P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z)))) _ _
  (@one_cat_native_homology_quotient_projection_reconstruction K C S C1 t T T0 P Q A B D f g z)) (@eq_trans _
  _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) B (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_boundary_transf K C S t T P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t T T0 A
  (@transf_arrow_diagram_func K C B D g) f z)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C A B) (@Transf K C A
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))) (λ v : τ (@Transf K
  C A B), (@comp_fapp0 (Functor_cat K C) A B (@cokernel_adjunction_family_func K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@transf_arrow_diagram_func K C A B f)) v)) _ _ (@one_cat_native_homology_quotient_boundary_reconstruction K
  C S C1 t T T0 P Q A B D f g z)) (@eq_trans _ _ _ _ (@one_cat_cokernel_family_annihilation_path K C S C1 t T
  T0 Q (@transf_arrow_diagram_func K C A B f)) (@eq_sym _ _ _ (@one_cat_zero_family_postcompose_path K C C1 t
  T T0 A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f))
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))))))))));

// k:H⇒K(ḡ) is the original whole Q descent, retaining H=Q(β).
symbol one_cat_native_homology_quotient_comparison [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@Transf K C (@homology_adjunction_family_func K C S t T T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z))))
≔ (@one_cat_cokernel_family_descent K C S C1 t T T0 Q (@kernel_adjunction_family_boundary_diagram_func K C S t
  T
  P A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t T T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K
  C A B f)) D (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_projection_boundary_zero K C S C1 t T T0 P Q A B D f g z));

// The original H quotient reconstructs k∘π_β=ρ.
symbol one_cat_native_homology_quotient_comparison_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  T T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))) (@comp_fapp0 (Functor_cat K
  C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C S t T T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C S C1 t T T0 P Q A B D f g z)
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@kernel_adjunction_family_boundary_diagram_func
  K C S t T P A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t T T0 A
  (@transf_arrow_diagram_func K C B D g) f z)))) (@one_cat_native_homology_quotient_projection K C S C1 t T T0
  P Q A B D f g z))
≔ (@one_cat_cokernel_family_descent_ambient_reconstruction K C S C1 t T T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C S C1 t T T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C S C1 t T T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_projection_boundary_zero K C S C1 t T T0 P Q A B D f g z));
