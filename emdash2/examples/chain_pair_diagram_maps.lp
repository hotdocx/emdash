require open emdash.emdash3_2_chain_pair_diagram_maps;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
    (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m)
  ≡ @computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
    (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m)
  ≡ @computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 m;


assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp0 _ _ (@chain_pair_outgoing_diagram_map_func C S C1 A0 B0 D0 A1 B1 D1 p0 p1) m
  ≡ @chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m;

// The old equality-valued map parameter retains its whole next Hom action.
type λ C : Cat, λ S : τ (@PreadditiveCategory C),
  λ C1 : τ (IsNCat (cat_succ cat_zero) C),
  λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ D0 : τ (Obj C),
  λ A1 : τ (Obj C), λ B1 : τ (Obj C), λ D1 : τ (Obj C),
  λ p0 : τ (@ComputationalChainPair C S A0 B0 D0),
  λ p1 : τ (@ComputationalChainPair C S A1 B1 D1),
  λ m0 : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1),
  λ m1 : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1),
  @fapp1_func _ _ (@chain_pair_outgoing_diagram_map_func C S C1 A0 B0 D0 A1 B1 D1 p0 p1) m0 m1;
