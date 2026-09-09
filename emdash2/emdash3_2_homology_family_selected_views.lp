require open emdash.emdash3_2_homology_families;
require open emdash.emdash3_2_kernel_adjunction_mates;

// The old selected construction at one point: the same kernel, its lift of
// the derived incoming test, and the same chosen cokernel family.
symbol homology_family_selected_boundary [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B))
  : τ (Hom C (@fapp0 B C A b)
      (@kernel_presentation_selected_object C S W (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)))
≔ @kernel_presentation_lift_semantic C S t T W (@fapp0 B C A b)
    (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)
    (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C)
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D b h);

symbol homology_family_selected_object [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B)) : τ (Obj C)
≔ @computational_cokernel_object C S (@fapp0 B C A b)
    (@kernel_presentation_selected_object C S W (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
    (@homology_family_selected_boundary B C S t T W A D h b)
    (V (@fapp0 B C A b)
      (@kernel_presentation_selected_object C S W (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
      (@homology_family_selected_boundary B C S t T W A D h b));

// Boundary inputs use only the object carrier of existing PathOut(C,A[b]).
// No extra carrier owner or Sigma-Hom action is required for this congruence.
symbol homology_family_boundary_data_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B))
  : τ (@= (Obj (@PathOut_cat C (@fapp0 B C A b)))
      (@Struct_sigma (Obj C) (λ Y : τ (Obj C), Hom C (@fapp0 B C A b) Y)
        (@fapp0 _ _ (@kernel_family_func B C S t T W P D) b)
        (@tapp0_fapp0 B C A (@kernel_family_func B C S t T W P D) b
          (@kernel_family_boundary_transf B C S t T W P A D h)))
      (@Struct_sigma (Obj C) (λ Y : τ (Obj C), Hom C (@fapp0 B C A b) Y)
        (@kernel_presentation_selected_object C S W (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
        (@homology_family_selected_boundary B C S t T W A D h b)))
≔ @eq_refl (Obj (@PathOut_cat C (@fapp0 B C A b)))
    (@Struct_sigma (Obj C) (λ Y : τ (Obj C), Hom C (@fapp0 B C A b) Y)
      (@fapp0 _ _ (@kernel_family_func B C S t T W P D) b)
      (@tapp0_fapp0 B C A (@kernel_family_func B C S t T W P D) b
        (@kernel_family_boundary_transf B C S t T W P A D h)));

// Ordinary congruence of the original dependent selection. Packaging its
// target/arrow input avoids asking unification to propagate through V.
symbol homology_family_object_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B))
  : τ (@= (Obj C) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b)
      (@homology_family_selected_object B C S t T W V A D h b))
≔ @eq_trans (Obj C) _ _ _
    (@cokernel_presentation_object_path C S t T0 V Q
      (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b))
    (@eq_ap (Obj (@PathOut_cat C (@fapp0 B C A b))) (Obj C)
      (λ z : τ (Obj (@PathOut_cat C (@fapp0 B C A b))),
        @computational_cokernel_object C S (@fapp0 B C A b)
          (sigma_Fst z) (sigma_Snd z)
          (V (@fapp0 B C A b) (sigma_Fst z) (sigma_Snd z)))
      (@Struct_sigma (Obj C) (λ Y : τ (Obj C), Hom C (@fapp0 B C A b) Y)
        (@fapp0 _ _ (@kernel_family_func B C S t T W P D) b)
        (@tapp0_fapp0 B C A (@kernel_family_func B C S t T W P D) b
          (@kernel_family_boundary_transf B C S t T W P A D h)))
      (@Struct_sigma (Obj C) (λ Y : τ (Obj C), Hom C (@fapp0 B C A b) Y)
        (@kernel_presentation_selected_object C S W (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
        (@homology_family_selected_boundary B C S t T W A D h b))
      (@homology_family_boundary_data_path B C S t T W P A D h b));

/* Compare whole H action using the established selected map theorem. */
symbol homology_family_map_path [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c))
  : τ (@= (Hom C (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) c))
      (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b c p)
      (@cokernel_presentation_map_semantic C S V (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) c) (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b c p)))
≔ @cokernel_presentation_map_path C S t T0 V Q (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) c) (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b c p);
