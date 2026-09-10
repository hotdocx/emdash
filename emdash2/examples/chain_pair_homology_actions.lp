/* These aliases observe the existing whole H action, not another map algorithm. */
require open emdash.emdash3_2_chain_pair_homology_actions;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @hom_precomp_factor_arrow C (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0
    B0 D0 p0)) (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
    (@homology_record_projection C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0)) (@comp_fapp0 C
    (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_cycle_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
    (@homology_record_projection C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
    (@chain_pair_homology_cycle_action C S C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m)) (@chain_pair_homology_action_factor C S C1 t T T0
    W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m)
  ≡ (@chain_pair_homology_action C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m);

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @hom_postcomp_factor_arrow C (@homology_record_cycle_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1
    B1 D1 p1)) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_cycle_embedding C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)) (@comp_fapp0
    C (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0)) B0 B1
    (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0 D0 p0
    (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))) (@chain_pair_homology_cycle_action_factor C S C1 t T T0 W V P
    Q A0 B0 D0 A1 B1 D1 p0 p1 m)
  ≡ (@chain_pair_homology_cycle_action C S C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m);

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  (@chain_pair_homology_action C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m)
  ≡ @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T
    W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1) (@chain_pair_zero_cone_map C S C1 t T W P A0 B0 D0 A1 B1 D1 p0
    p1 m);

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (zero : τ (@= (Hom C B0 B1) (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@preadditive_hom_zero C S B0
    B1))) ⊢
  @chain_pair_homology_action_middle_zero C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m zero
  : τ (@= (Hom C (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)))
    (@chain_pair_homology_action C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m) (@preadditive_hom_zero C S
    (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))));

assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (other : τ (Hom C
    (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)))) ⊢
  @eq_refl (Hom C (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)))
    (@chain_pair_homology_action C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m)
  : τ (@= (Hom C (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)))
    (@chain_pair_homology_action C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m) other);
