/* Point views retain the original whole kernel action and native diagram projection. */
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_maps;
require open emdash.emdash3_2_whiskering_component_paths;
require open emdash.emdash3_2_one_cat_zero_cones;

symbol kernel_family_map_at_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (D E : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (m : τ (@Transf B (Functor_cat WalkingArrow_cat C) D E)) (x : τ (Obj B))
 : τ (@= (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x)
  (@fapp0 B C (@kernel_adjunction_family_func B C S t T P E) x))
 (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P E) x
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))
 (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) (@fapp0 B (Functor_cat WalkingArrow_cat C) E x)
  (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) D E x m)))
≔ @postwhisker_native_source_component_path B (Functor_cat WalkingArrow_cat C) C
 (@kernel_adjunction_func C S t T P) D E m x;

symbol native_kernel_map_diagram_path [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 (P : τ (@KernelAdjunctionStructure C S t T))
 [X Y : τ (Obj (@ZeroArrowCone_cat C t T))] (n : τ (Hom (@ZeroArrowCone_cat C t T) X Y))
 : τ (@= (Hom C
 (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) X)
 (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) Y))
 (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) X Y n)
 (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) X)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) Y)
  (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) X Y n)))
≔ @eq_refl _
 (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) X)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) Y)
  (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) X Y n));
