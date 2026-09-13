/* Exactness evidence is fixed to the constructed comparison; it is not supplied automatically. */
require open emdash.emdash3_2_one_cat_categorical_exactness;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (E : τ (@OneCatAdjunctionExactFamily B C S C1 t T T0 P Q A D
    h N))
  ⊢ E : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N));

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (b : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D))) (Eb : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t
    T A D h)) (@kernel_adjunction_family_func B C S t T P D) b))
  ⊢ Eb : τ (@OneCatAdjunctionExactFamily B C S C1 t T T0 P Q A D h N);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (E : τ (@OneCatAdjunctionExactFamily B C S C1 t T T0 P Q A D
    h N)) (b : τ (Obj B))
  ⊢ @omega_equiv_along_fapp1_fapp0 (Functor_cat B C) C (@fapp0_func B C b) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) E
    : τ (@OmegaEquivAlong C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
      C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@kernel_adjunction_family_func
      B C S t T P D) b) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
      (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
      (@kernel_adjunction_family_func B C S t T P D) b (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h
      N)));

assert [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ (@zero_arrow_cone_image_kernel_transf C S C1 t T T0 P Q N) : τ (@Transf (@ZeroArrowCone_cat C t T) C
    (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0
    P Q) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
    (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))
    (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)));

assert [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (z : τ (Obj (@ZeroArrowCone_cat C t T)))
  ⊢ @tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
    (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T
    P (@zero_arrow_cone_diagram_func C t T)) z (@zero_arrow_cone_image_kernel_transf C S C1 t T T0 P Q N) : τ (Hom C
    (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t
    T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1
    t T)) z)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) z)));

assert [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (z z0 : τ (Obj (@ZeroArrowCone_cat C t T)))
  ⊢ @tapp1_func (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat
    C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1
    t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T))
    z z0 (@zero_arrow_cone_image_kernel_transf C S C1 t T T0 P Q N) : τ (Functor (Hom_cat (@ZeroArrowCone_cat C t T) z
    z0) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
    (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T))) z) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) z0)));
