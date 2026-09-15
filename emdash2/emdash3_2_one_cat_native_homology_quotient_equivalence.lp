/* Original H=Q(β) to K(ḡ) equivalence through native cover descent. */
require open emdash.emdash3_2_one_cat_native_homology_quotient_image;
require open emdash.emdash3_2_one_cat_native_homology_quotient_covers;
require open emdash.emdash3_2_one_cat_coimage_cover_descent;

// The original whole image source cover makes π_β kill the image lift.
symbol one_cat_native_homology_quotient_image_homology_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero)
  C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) (@homology_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@one_cat_native_homology_quotient_image_lift
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func
  K C A B f))) (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))))
≔ (@one_cat_image_family_source_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@transf_arrow_diagram_func K C A B f)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q)
  (@transf_arrow_diagram_func K C A B f))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@one_cat_native_homology_quotient_image_lift K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func
  K C A B f))) (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K
  C) A (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func
  K C A B f))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@one_cat_native_homology_quotient_image_lift K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C A B f)))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C A (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))) (@Transf K C A
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (λ v : τ
  (@Transf K C A (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))), (@comp_fapp0
  (Functor_cat K C) A (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) v)) _ _ (@one_cat_native_homology_quotient_image_boundary_path
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))
  (@eq_trans _ _ _ _ (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func
  K C A B f))) (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@one_cat_image_family_source_transf K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C A B
  f))))))));

// Original image and cycle reconstruction prove π_β∘κ_ρ=0, without a supplied annihilation.
symbol one_cat_native_homology_quotient_projection_kernel_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero)
  C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@kernel_adjunction_family_inclusion_transf K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g))) (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) v)) _ _ (@eq_sym _ _ _
  (@one_cat_native_homology_quotient_kernel_cycle_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat
  K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@one_cat_native_homology_quotient_image_lift
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_kernel_image_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func
  K C A B f))) (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func
  K C A B f))) (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) v
  (@one_cat_native_homology_quotient_kernel_image_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) _ _
  (@one_cat_native_homology_quotient_image_homology_zero K C C1 Prod t Add T0 P Q N A B D f g z))
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K C A B f)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_kernel_image_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))));

// The existing native cover descent constructs s:K(ḡ)⇒H from the original π_β.
symbol one_cat_native_homology_quotient_comparison_inverse [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)))
≔ (@one_cat_coimage_cover_descent K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))
  (@one_cat_native_homology_quotient_projection_cover_omega K C C1 Prod t Add T0 P Q N A B D f g z)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@one_cat_native_homology_quotient_projection_kernel_zero K C
  C1 Prod t Add T0 P Q N A B D f g z));

// The original cover reconstructs s∘ρ=π_β.
symbol one_cat_native_homology_quotient_comparison_inverse_reconstruction [K C : Cat] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))))
≔ (@one_cat_coimage_cover_descent_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))
  (@one_cat_native_homology_quotient_projection_cover_omega K C C1 Prod t Add T0 P Q N A B D f g z)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@one_cat_native_homology_quotient_projection_kernel_zero K C
  C1 Prod t Add T0 P Q N A B D f g z));

// The original H quotient cancels to prove s∘k=id_H.
symbol one_cat_native_homology_quotient_comparison_inverse_forward [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  : τ (@= (@Transf K C (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@homology_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@comp_fapp0 (Functor_cat K C)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)) (@id (Functor_cat K C)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))))
≔ (@one_cat_cokernel_family_quotient_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@comp_fapp0 (Functor_cat K C)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)) (@id (Functor_cat K C)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@eq_trans _ _ _
  _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))))
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (λ v : τ
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))),
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z) v)) _ _
  (@one_cat_native_homology_quotient_comparison_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))
  (@one_cat_native_homology_quotient_comparison_inverse_reconstruction K C C1 Prod t Add T0 P Q N A B D f g
  z))));

// The derived original cycle cover cancels to prove k∘s=id_K(ḡ).
symbol one_cat_native_homology_quotient_comparison_forward_inverse [K C : Cat] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)) (@id
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))))
≔ (@one_cat_native_homology_quotient_projection_reflect_path K C C1 Prod t Add T0 P Q N A B D f g z
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)) (@id
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@Transf K C (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))) (λ
  v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) v)) _ _
  (@one_cat_native_homology_quotient_comparison_inverse_reconstruction K C C1 Prod t Add T0 P Q N A B D f g
  z)) (@one_cat_native_homology_quotient_comparison_reconstruction K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))));

// Fixed-forward ΩAlong(k) retains the original H and original quotient-differential kernel.
symbol one_cat_native_homology_quotient_comparison_equiv [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  : τ (@OmegaEquivAlong (Functor_cat K C) (@homology_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))
≔ (@omega_equiv_along_intro (Functor_cat K C) (@homology_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_comparison_inverse_forward K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_comparison_forward_inverse K C C1 Prod t Add T0 P Q N A B D f g z));
