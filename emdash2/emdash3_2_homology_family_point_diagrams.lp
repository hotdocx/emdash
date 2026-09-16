/* Categorical comparison of the same original H-boundary diagrams. */
require open emdash.emdash3_2_zero_arrow_family_point_inputs;
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;
require open emdash.emdash3_2_homology_adjunction_input_data;
require open emdash.emdash3_2_one_cat_diagram_map_equivalences;

// The original semantic boundary supplies the generator equality; endpoints are identities.
symbol homology_family_global_boundary_point_map [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 : τ (@Transf WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
≔ @one_cat_original_diagram_map C C1 (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@id C
  (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_src)) (@id C
  (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt))
 (@path_to_hom (Hom_cat C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_src) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt)) (@fapp1_fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat
  C t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@eq_refl (Hom C (@fapp0 WalkingArrow_cat C
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P
  A D h) x) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt)) (@fapp1_fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)));

// Both original boundary objects and the same forward transformation are retained.
symbol homology_family_global_boundary_point_equiv [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 : τ (@OmegaEquivAlong (Functor_cat WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@homology_family_global_boundary_point_map K C S C1 t T P A D h x))
≔ @one_cat_diagram_map_equiv C C1 (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@homology_family_global_boundary_point_map K C S C1 t T P A D h x)
 (@omega_equiv_along_refl C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_src))
  (@omega_equiv_along_refl C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt));
