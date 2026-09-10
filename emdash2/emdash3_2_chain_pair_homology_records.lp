/* Whole-H records for ORIGINAL raw input pairs, with no endpoint conversion. */
require open emdash.emdash3_2_homology_family_records;
require open emdash.emdash3_2_chain_pair_zero_cone_comparisons;

symbol chain_pair_homology_boundary_diagram [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Functor WalkingArrow_cat C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@kernel_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T W P
      (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
      (@zero_arrow_cone_universal_transf C C1 t T))
    (@chain_pair_zero_cone C S t T W P A B D pair);

symbol chain_pair_homology_boundary_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair)
    (@fapp0 _ _ (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair)) (@tapp0_fapp0 _ _ _ _ (@chain_pair_outgoing_diagram C S A B D pair) (@kernel_presentation_inclusion C S t T W P)) A (@computational_chain_pair_cone C S A B D pair))
≔ @Struct_sigma (Hom C A (@fapp0 _ _ (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair)))
    (λ f : τ (Hom C A (@fapp0 _ _ (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair))), @= (Hom C A B)
      (@comp_fapp0 C A (@fapp0 _ _ (@kernel_presentation_func C S t T W P) (@chain_pair_outgoing_diagram C S A B D pair)) B (@tapp0_fapp0 _ _ _ _ (@chain_pair_outgoing_diagram C S A B D pair) (@kernel_presentation_inclusion C S t T W P)) f)
      (@computational_chain_pair_dnext C S A B D pair))
    (@kernel_semantic_boundary C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair) (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair))
  (@chain_pair_selected_boundary C S W A B D pair)))
    (@eq_trans (Hom C A B) _ _ _
      (@kernel_semantic_boundary_reconstruction C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair) (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair))
  (@chain_pair_selected_boundary C S W A B D pair)))
      (@chain_pair_zero_cone_incoming_path C S t T W P A B D pair));

symbol chain_pair_homology_record [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@HomologyRecord C S A B D pair)
≔ @homology_record_intro C S A B D pair
    (@kernel_presentation_record C S t T W P (@chain_pair_outgoing_diagram C S A B D pair))
    (@chain_pair_homology_boundary_factor C S t T W P A B D pair)
    (@cokernel_presentation_record C S t T0 V Q (@chain_pair_homology_boundary_diagram C S C1 t T W P A B D pair));
