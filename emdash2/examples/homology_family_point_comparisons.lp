/* The categorical point comparison retains both H objects and the chosen inverse. */
require open emdash.emdash3_2_homology_family_point_comparisons;
symbol K : Cat;
symbol C : Cat;
symbol t : τ (Obj C);
symbol T : τ (@TerminalObject C t);
symbol A : τ (Functor K C);
symbol D : τ (Functor K (Functor_cat WalkingArrow_cat C));
symbol h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D);
symbol x : τ (Obj K);
symbol S : τ (@PreadditiveCategory C);
symbol C1 : τ (IsNCat (cat_succ cat_zero) C);
symbol T0 : τ (@TerminalObject (Op_cat C) t);
symbol P : τ (@KernelAdjunctionStructure C S t T);
symbol Q : τ (@CokernelAdjunctionStructure C S t T0);
assert ⊢ (@homology_family_global_point_map K C S C1 t T T0 P Q A D h x) : τ (Hom C (@fapp0 K C
  (@homology_adjunction_family_func K C S t T T0 P Q A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input K C t T A D h
  x)));
assert ⊢ (@homology_family_global_point_equiv K C S C1 t T T0 P Q A D h x) : τ (@OmegaEquivAlong C (@fapp0 K C
  (@homology_adjunction_family_func K C S t T T0 P Q A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input K C t T A D h
  x)) (@homology_family_global_point_map K C S C1 t T T0 P Q A D h x));
assert ⊢ @omega_equiv_along_left_inv C (@fapp0 K C (@homology_adjunction_family_func K C S t T T0 P Q A D h) x)
  (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input K C t T A D h x)) (@homology_family_global_point_map K C S C1 t T T0 P Q A D h
  x) (@homology_family_global_point_equiv K C S C1 t T T0 P Q A D h x) ≡ @fapp1_fapp0 (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@path_to_hom (Functor_cat
  WalkingArrow_cat C) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@path_sym (Functor WalkingArrow_cat C)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)
  x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@homology_family_global_boundary_point_path K C S
  C1 t T P A D h x)));
assert ⊢ @fapp1_func (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) : τ (Functor (Hom_cat (Functor_cat WalkingArrow_cat
  C) (@fapp0 K (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D
  h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (Hom_cat C (@fapp0 K C
  (@homology_adjunction_family_func K C S t T T0 P Q A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input K C t T A D h
  x))));
