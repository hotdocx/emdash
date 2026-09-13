/* Direct native maps retain all original components without K/P parameters. */
require open emdash.emdash3_2_one_cat_chain_pair_native_maps;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1) (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m)
  ≡ @computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 m;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1) (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m)
  ≡ @chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
    (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
      (@zero_arrow_cone_diagram_func C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1) (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m))
  ≡ @computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
    (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
      (@zero_arrow_cone_diagram_func C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1) (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m))
  ≡ @computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp0 _ _ (@chain_pair_native_map_func C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1) m
  ≡ (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m);

assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (other : τ (Hom (@ZeroArrowCone_cat C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1))) ⊢
  eq_refl (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m) : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)) (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m) other);

// Whole action is retained in the existing raw-map path category.
type λ C : Cat, λ S : τ (@PreadditiveCategory C),
  λ C1 : τ (IsNCat (cat_succ cat_zero) C), λ t : τ (Obj C),
  λ T : τ (@TerminalObject C t),
  λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ D0 : τ (Obj C),
  λ A1 : τ (Obj C), λ B1 : τ (Obj C), λ D1 : τ (Obj C),
  λ p0 : τ (@ComputationalChainPair C S A0 B0 D0),
  λ p1 : τ (@ComputationalChainPair C S A1 B1 D1),
  λ m0 : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1),
  λ m1 : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1),
  @fapp1_func _ _ (@chain_pair_native_map_func C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1) m0 m1;
