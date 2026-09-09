require open emdash.emdash3_2_kernel_adjunction_unmate_paths;
require open emdash.emdash3_2_chain_pair_zero_cones;
require open emdash.emdash3_2_zero_arrow_cone_homology;

// The reconstructed incoming arrow agrees with the original by universality.
symbol chain_pair_zero_cone_incoming_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@= (Hom C A B)
      (@terminal_arrow_test_incoming C t T A (@chain_pair_outgoing_diagram C S A B D pair) (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair)) (@chain_pair_selected_boundary C S W A B D pair))) (@computational_chain_pair_dnext C S A B D pair))
≔ @kernel_presentation_unlift_lift_source_path C S t T W P A
    (@chain_pair_outgoing_diagram C S A B D pair)
    (@computational_chain_pair_cone C S A B D pair);

/* Native global H retains the original selected boundary at raw entry. */

symbol chain_pair_zero_cone_boundary_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@= (Hom C A (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair))) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A B D pair) (@kernel_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))) (@chain_pair_selected_boundary C S W A B D pair))
≔ @kernel_presentation_semantic_unlift_beta_path C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair) (@chain_pair_selected_boundary C S W A B D pair);

/* Whole H at an original chain input agrees with its selected recipe. */

// Pair the target with its arrow before applying the dependent selector.
symbol chain_pair_zero_cone_boundary_data_path [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@= (Obj (@PathOut_cat C A)) (@Struct_sigma (Obj C) (λ M : τ (Obj C), Hom C A M) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair)) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A B D pair) (@kernel_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))) (@Struct_sigma (Obj C) (λ M : τ (Obj C), Hom C A M) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair)
  (W B D (@computational_chain_pair_d C S A B D pair))) (@chain_pair_selected_boundary C S W A B D pair)))
≔ @eq_ap (Hom C A (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair))) (Obj (@PathOut_cat C A))
    (λ f : τ (Hom C A (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair))), (@Struct_sigma (Obj C) (λ M : τ (Obj C), Hom C A M) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair)) f))
    (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A B D pair) (@kernel_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))) (@chain_pair_selected_boundary C S W A B D pair)
    (@chain_pair_zero_cone_boundary_path C S C1 t T W P A B D pair);

symbol chain_pair_zero_cone_homology_object_path [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@= (Obj C) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W P A B D pair)) (@computational_cokernel_object C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair)
  (W B D (@computational_chain_pair_d C S A B D pair))) (@chain_pair_selected_boundary C S W A B D pair) (V A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair)
  (W B D (@computational_chain_pair_d C S A B D pair))) (@chain_pair_selected_boundary C S W A B D pair))))
≔ @eq_trans (Obj C) _ _ _
    (@cokernel_presentation_object_path C S t T0 V Q
      (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@chain_pair_zero_cone C S t T W P A B D pair)))
    (@eq_ap (Obj (@PathOut_cat C A)) (Obj C)
      (λ input : τ (Obj (@PathOut_cat C A)),
        @computational_cokernel_object C S A (sigma_Fst input) (sigma_Snd input)
          (V A (sigma_Fst input) (sigma_Snd input)))
      (@Struct_sigma (Obj C) (λ M : τ (Obj C), Hom C A M) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair)) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A B D pair) (@kernel_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))) (@Struct_sigma (Obj C) (λ M : τ (Obj C), Hom C A M) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair)
  (W B D (@computational_chain_pair_d C S A B D pair))) (@chain_pair_selected_boundary C S W A B D pair))
      (@chain_pair_zero_cone_boundary_data_path C S C1 t T T0 W V P Q A B D pair));
