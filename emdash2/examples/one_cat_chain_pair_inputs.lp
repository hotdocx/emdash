/* Original raw input observations, with no K/Q or selected capabilities. */
require open emdash.emdash3_2_one_cat_chain_pair_inputs;
require open emdash.emdash3_2_one_cat_zero_cones;
require open emdash.emdash3_2_zero_arrow_diagram_observations;

// The native first vertex is the original A.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@chain_pair_native_cone C S C1 t T A B D pair)
  ≡ A;

// The native outgoing diagram keeps the original differential.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@chain_pair_native_cone C S C1 t T A B D pair)
  ≡ (@chain_pair_outgoing_diagram C S A B D pair);

// The whole universal observation returns the constructed transformation.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @tapp0_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) _ _
    (@chain_pair_native_cone C S C1 t T A B D pair) (@zero_arrow_cone_universal_transf C C1 t T)
  ≡ (@chain_pair_native_transf C S C1 t T A B D pair);

// The input transformation has the original incoming differential.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @terminal_arrow_test_incoming C t T A (@chain_pair_outgoing_diagram C S A B D pair) (@chain_pair_native_transf C S C1 t T A B D pair)
  ≡ @computational_chain_pair_dnext C S A B D pair;

// The outgoing diagram generator is the original d.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp1_fapp0 WalkingArrow_cat C (@chain_pair_outgoing_diagram C S A B D pair) walking_arrow_src walking_arrow_tgt walking_arrow_generator
  ≡ @computational_chain_pair_d C S A B D pair;
