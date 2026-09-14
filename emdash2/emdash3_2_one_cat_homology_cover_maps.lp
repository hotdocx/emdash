/* Original H quotient and the canonical map from the kernel pullback.
   These construct the map ρ. Epicity of r remains a proof
   obligation from the original short-exact input and Abelian normality. */
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_kernel_pullback_universality;

// q_H is the original quotient of the original whole boundary diagram.
symbol homology_adjunction_family_projection_transf [B C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A
    D h))
≔ @cokernel_adjunction_family_projection_transf B C S t T0 Q (@kernel_adjunction_family_boundary_diagram_func B
  C S t T P A D h);

// Original whole homology quotient cancellation follows from its native Q.
symbol one_cat_homology_projection_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (Y : τ (Functor B C)) (u v : τ (@Transf B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y))
  (e : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) Y) (@comp_fapp0 (Functor_cat B C)
    (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y u
    (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h)) (@comp_fapp0 (Functor_cat B C)
    (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y v
    (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h))))
  : τ (@= (@Transf B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y) u v)
≔ @one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) Y u v e;

// ρ=q_H∘r uses the proved original kernel square and original H.
symbol one_cat_homology_cover_transf [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (X : τ (Functor B C)) (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  : τ (@Transf B C (@kernel_precomposition_family_func B C S t T P X D p) (@homology_adjunction_family_func B C S t T
    T0 P Q A D h))
≔ (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p)
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h)
  (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p));
