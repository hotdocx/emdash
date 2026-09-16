/* Canonical Coim/Im→Ker compatibility at the same native point input.
   Whole reconstruction, projection naturality and existing equivalence
   cancellation supply every equation; no commutativity is an input. */
require open emdash.emdash3_2_image_family_point_comparisons;
require open emdash.emdash3_2_coimage_family_point_comparisons;
require open emdash.emdash3_2_one_cat_cokernel_point_cancellation;
require open emdash.emdash3_2_one_cat_image_kernel_inclusion_paths;
require open emdash.emdash3_2_strict_transfor_component_paths;
require open emdash.emdash3_2_omega_equiv_cancellation_paths;

// Whole projection naturality gives Coim(c)∘π₀ = π₁.
symbol one_cat_coimage_point_projection_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))

 : τ (@= (Hom C (@fapp0 K C A x) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0
  P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))) (@comp_fapp0 C (@fapp0 K C A x) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@coimage_family_global_point_map K C S C1 t T T0
  P Q A D h x) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@adjunction_coimage_projection C S t T T0 P Q)))
  (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@adjunction_coimage_projection C S t T T0 P Q)))
≔ @eq_trans _ _ _ _ (@strict_component_naturality_path (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_coimage_projection C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@zero_arrow_family_point_diagram_map K C C1 t T A D h x))
 (@eq_ap (Hom C (@fapp0 K C A x) (@fapp0 K C A x)) (Hom C (@fapp0 K C A x) (@fapp0 (Functor_cat WalkingArrow_cat
  C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))))
   (λ k : τ (Hom C (@fapp0 K C A x) (@fapp0 K C A x)), @comp_fapp0 C (@fapp0 K C A x) (@fapp0 K C A x) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@adjunction_coimage_projection C S t T T0 P Q)) k)
  _ _
   (@zero_arrow_family_point_diagram_map_src_path K C C1 t T A D h x));

// Both kernel-boundary observations use the same native point input.
symbol one_cat_kernel_boundary_global_point_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T))
 (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
 (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 K C A x) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x)) (@tapp0_fapp0 K
  C A (@kernel_adjunction_family_func K C S t T P D) x (@kernel_adjunction_family_boundary_transf K C S t T P A
  D h)) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T))
  (@zero_arrow_family_point_input K C t T A D h x) (@kernel_adjunction_family_boundary_transf
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))))
≔ @eq_refl (Hom C (@fapp0 K C A x) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x)) (@tapp0_fapp0
  K C A (@kernel_adjunction_family_func K C S t T P D) x (@kernel_adjunction_family_boundary_transf K C S t T P
  A D h));

// Evaluate the original whole coimage descent reconstruction.
symbol one_cat_coimage_kernel_point_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
 (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 K C A x) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x)) (@comp_fapp0 C
  (@fapp0 K C A x) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0
  K (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C
  (@kernel_adjunction_family_func K C S t T P D) x) (@tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K C t T A D
  h)) (@kernel_adjunction_family_func K C S t T P D) x (@one_cat_coimage_to_kernel_transf K C S C1 t T T0 P Q A
  D h)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@adjunction_coimage_projection C S t T T0 P Q)))
  (@tapp0_fapp0 K C A (@kernel_adjunction_family_func K C S t T P D) x
  (@kernel_adjunction_family_boundary_transf K C S t T P A D h)))
≔ @eq_ap (@Transf K C A (@kernel_adjunction_family_func K C S t T P D)) (Hom C (@fapp0 K C A x) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x))
  (λ v : τ (@Transf K C A (@kernel_adjunction_family_func K C S t T P D)), @tapp0_fapp0 K C A (@kernel_adjunction_family_func K C S t T P D) x v) _ _
  (@one_cat_coimage_kernel_ambient_reconstruction K C S C1 t T T0 P Q A D h);

// Cancel the original quotient after reconstruction and its whole naturality.
symbol one_cat_coimage_kernel_point_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C
  (@kernel_adjunction_family_func K C S t T P D) x)) (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_coimage_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C
  t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))
  (@coimage_family_global_point_map K C S C1 t T T0 P Q A D h x)) (@tapp0_fapp0 K C (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  K C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x (@one_cat_coimage_to_kernel_transf K C S C1 t
  T T0 P Q A D h)))
≔ (@one_cat_cokernel_quotient_reflect_path C S C1 t T T0 Q (@fapp0 K C (@kernel_adjunction_family_func K C S t T
  P D) x) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_coimage_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C
  t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))
  (@coimage_family_global_point_map K C S C1 t T T0 P Q A D h x)) (@tapp0_fapp0 K C (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  K C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x (@one_cat_coimage_to_kernel_transf K C S C1 t
  T T0 P Q A D h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C (@fapp0 K C A x) (@fapp0 (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_coimage_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C
  t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))
  (@coimage_family_global_point_map K C S C1 t T T0 P Q A D h x) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C)
  C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)
  (@adjunction_coimage_projection C S t T T0 P Q)))) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@fapp0 K C A x) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))) (Hom C (@fapp0 K C A x) (@fapp0 K C
  (@kernel_adjunction_family_func K C S t T P D) x)) (λ q : τ (Hom C (@fapp0 K C A x) (@fapp0 (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))), (@comp_fapp0 C (@fapp0 K C A x) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S
  t T P D) x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_coimage_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C
  t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))) q)) _ _
  (@one_cat_coimage_point_projection_path K C S C1 t T T0 P Q A D h x)) (@eq_trans _ _ _ _
  (@one_cat_coimage_kernel_point_reconstruction (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T) (@zero_arrow_family_point_input K C t T A D h x)) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@one_cat_kernel_boundary_global_point_path K C S C1 t T P A D h x)) (@eq_sym _ _ _
  (@one_cat_coimage_kernel_point_reconstruction K C S C1 t T T0 P Q A D h x)))))));

// Evaluate the original whole e∘α = coimage-factor equation.
symbol one_cat_image_kernel_point_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C
  (@kernel_adjunction_family_func K C S t T P D) x)) (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P
  D) x) (@tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T
  T0 P Q) (@zero_arrow_family_incoming_func K C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x
  (@one_cat_image_to_kernel_transf K C S C1 t T T0 P Q A D h N)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C)
  C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x) (@one_cat_coimage_image_comparison C S
  C1 t T T0 P Q))) (@tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K C t T A D h))
  (@kernel_adjunction_family_func K C S t T P D) x (@one_cat_coimage_to_kernel_transf K C S C1 t T T0 P Q A D
  h)))
≔ @eq_ap (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0
  P Q) (@zero_arrow_family_incoming_func K C t T A D h)) (@kernel_adjunction_family_func K C S t T P D)) (Hom C
  (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C
  (@kernel_adjunction_family_func K C S t T P D) x))
   (λ v : τ (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T
  T0 P Q) (@zero_arrow_family_incoming_func K C t T A D h)) (@kernel_adjunction_family_func K C S t T P D)),
  @tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func K C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x v) _ _
   (@one_cat_image_kernel_reconstruction_path K C S C1 t T T0 P Q A D h N);

// Coim⇒Im naturality and its existing fixed-forward equivalence give canonical compatibility.
symbol one_cat_image_kernel_point_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C
  (@kernel_adjunction_family_func K C S t T P D) x)) (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_image_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C t
  T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N))
  (@image_family_global_point_map K C S C1 t T T0 P Q A D h x)) (@tapp0_fapp0 K C (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K
  C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x (@one_cat_image_to_kernel_transf K C S C1 t T
  T0 P Q A D h N)))
≔ (@omega_equiv_precomp_reflect_path C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S
  t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x))
  (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@tapp0_fapp0 (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@omega_equiv_along_fapp1_fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) C (@fapp0_func (Functor_cat WalkingArrow_cat C) C (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@adjunction_coimage_func C S t T T0
  P Q) (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) N) (@fapp0
  K C (@kernel_adjunction_family_func K C S t T P D) x) (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C)
  C (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_image_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C t
  T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N))
  (@image_family_global_point_map K C S C1 t T T0 P Q A D h x)) (@tapp0_fapp0 K C (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K
  C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x (@one_cat_image_to_kernel_transf K C S C1 t T
  T0 P Q A D h N)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_image_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C t
  T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N))
  (@image_family_global_point_map K C S C1 t T T0 P Q A D h x) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x) (@one_cat_coimage_image_comparison C S
  C1 t T T0 P Q)))) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x)))) (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P
  D) x)) (λ v : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))), (@comp_fapp0 C (@fapp0 (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_image_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C t
  T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N)) v)) _ _
  (@strict_component_naturality_path (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@zero_arrow_family_point_diagram_map K C C1 t T A D h x))) (@eq_trans _ _ _ _ (@comp_assoc C (@fapp0 (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_image_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C t
  T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N)) (@tapp0_fapp0
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T
  T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@coimage_family_global_point_map K C S C1 t T T0 P Q A
  D h x)) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func
  C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x)) (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 K C
  (@kernel_adjunction_family_func K C S t T P D) x)) (λ v : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x)), (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S
  t T P D) x) v (@coimage_family_global_point_map K C S C1 t T T0 P Q A D h x))) _ _
  (@one_cat_image_kernel_point_reconstruction (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func
  C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N
  (@zero_arrow_family_point_input K C t T A D h x))) (@eq_trans _ _ _ _
  (@one_cat_coimage_kernel_point_path K C S C1 t T T0 P Q A D h x) (@eq_sym _ _ _
  (@one_cat_image_kernel_point_reconstruction K C S C1 t T T0 P Q A D h N x))))))));
