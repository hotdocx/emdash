/* Direct native maps from the original chain-map factor data.
   The ordinary comparison cell is derived internally. The native Hom keeps
   its represented postcomposition endpoint; the existing proof-time raw
   comparison is staged as a typed equality view. No new rule is introduced. */
require open emdash.emdash3_2_chain_pair_diagram_maps;
require open emdash.emdash3_2_one_cat_chain_pair_inputs;
require open emdash.emdash3_2_one_cat_diagram_map_paths;

// Typed view of the existing identity-family postcomposition comparison.
protected symbol native_identity_postcomp_raw_path [K : Cat]
  [x y z : τ (Obj K)] (g : τ (Hom K y z)) (f : τ (Hom K x y))
  : τ (@= (Hom K x z)
      (@hom_postcomp_fapp0 K K (@id_func K) x y z g f)
      (@comp_fapp0 K x y z g f))
≔ @eq_refl (Hom K x z)
    (@hom_postcomp_fapp0 K K (@id_func K) x y z g f);

// The two actual diagram composites requiring a native comparison.
protected symbol chain_pair_native_map_left [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1))
≔ @comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A0 B0 D0 p0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_transf C S C1 t T A0 B0 D0 p0);

protected symbol chain_pair_native_map_right [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1))
≔ @comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A1) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) (@chain_pair_native_transf C S C1 t T A1 B1 D1 p1)
    (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0 A1 (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 m));

// The original upper factor and terminal-zero property determine this cell.
protected symbol chain_pair_native_map_comparison_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1)) (@hom_postcomp_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A0 B0 D0 p0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_transf C S C1 t T A0 B0 D0 p0)) (@chain_pair_native_map_right C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m))
≔ @eq_trans (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1)) (@hom_postcomp_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A0 B0 D0 p0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_transf C S C1 t T A0 B0 D0 p0)) (@chain_pair_native_map_left C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_map_right C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@native_identity_postcomp_raw_path (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A0 B0 D0 p0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_transf C S C1 t T A0 B0 D0 p0))
    (@one_cat_diagram_map_path C C1 (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) (@chain_pair_native_map_left C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_map_right C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@eq_sym (Hom C A0 B1) _ _ (@computational_chain_pair_map_upper_path C S A0 B0 D0 A1 B1 D1 p0 p1 m))
    (@eq_trans (Hom C t D1) (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) walking_arrow_tgt (@chain_pair_native_map_left C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m)) (@preadditive_hom_zero C S t D1) (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) walking_arrow_tgt (@chain_pair_native_map_right C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m))
      (@preadditive_terminal_to_zero_path C S t D1 T (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) walking_arrow_tgt (@chain_pair_native_map_left C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m)))
      (@eq_sym (Hom C t D1) _ _ (@preadditive_terminal_to_zero_path C S t D1 T (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) walking_arrow_tgt (@chain_pair_native_map_right C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m))))));

// Existing native Hom constructor; no kernel/cokernel structure is involved.
symbol chain_pair_native_map [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom (@ZeroArrowCone_cat C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1))
≔ Struct_sigma (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 m) (Struct_sigma (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@path_to_hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1))
      (@hom_postcomp_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) (@chain_pair_outgoing_diagram C S A0 B0 D0 p0) (@chain_pair_outgoing_diagram C S A1 B1 D1 p1) (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_transf C S C1 t T A0 B0 D0 p0)) (@chain_pair_native_map_right C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_native_map_comparison_path C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m)));

// Whole action in the original equality-valued raw-map parameter.
symbol chain_pair_native_map_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : τ (Functor (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
      (Hom_cat (@ZeroArrowCone_cat C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)))
≔ @fapp0 _ _ (@path_lift_func (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)
    (Hom_cat (@ZeroArrowCone_cat C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)))
    (λ m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1), @chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m);
