/* Categorical exactness at the actual whole image-to-kernel comparison.
   This defines a condition, not an inhabitant or an LES exactness axiom.
   The comparison on all native zero-cones is not asserted invertible. */
require open emdash.emdash3_2_one_cat_image_kernel_comparison;
require open emdash.emdash3_2_one_cat_zero_cones;

// Exactness is existing fixed-forward OmegaEquivAlong evidence on this actual e.
symbol OneCatAdjunctionExactFamily [B C : Cat] [S : τ (@PreadditiveCategory C)]
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
  : Grpd
≔ @OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S
  t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N);

// Specialize e to the existing native zero-cone category and its whole tautological input.
symbol zero_arrow_cone_image_kernel_transf [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  : τ (@Transf (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat
    C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1
    t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
    T)))
≔ @one_cat_image_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N;
