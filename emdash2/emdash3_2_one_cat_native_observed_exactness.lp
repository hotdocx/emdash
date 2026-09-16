/* Observation indexing after canonical exactness has already been transported. */
require open emdash.emdash3_2_one_cat_categorical_exactness_points;
require open emdash.emdash3_2_zero_arrow_pair_observations;
require open emdash.emdash3_2_one_cat_kernel_input_pair_observations;

symbol native_input_pair_observation [C : Cat]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 (X : τ (Obj (@ZeroArrowCone_cat C t T))) : τ (ArrowPairObservation C)
≔ @zero_arrow_family_pair_at (@ZeroArrowCone_cat C t T) C t T
 (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
 (@zero_arrow_cone_universal_transf C C1 t T) X;

// The actual native input and canonical witness remain parameters, not existentially reselected data.
symbol NativeObservedPairExactAt [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (X : τ (Obj (@ZeroArrowCone_cat C t T)))
 (edge0 edge1 : τ (Obj (@LaxArrow_cat C))) : Grpd
≔ @Product_grpd (@OneCatNativeExactAt C S C1 t T T0 P Q N X)
 (@= (ArrowPairObservation C) (@native_input_pair_observation C C1 t T X) (Struct_sigma edge0 edge1));

// Reuse the canonical witness; only its observation path is extended by the actual interpretation path.
symbol native_observed_pair_exact_transport [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (X : τ (Obj (@ZeroArrowCone_cat C t T)))
 [a0 a1 b0 b1 : τ (Obj (@LaxArrow_cat C))]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X a0 a1))
 (p : τ (@= (Obj (@LaxArrow_cat C)) a0 b0))
 (q : τ (@= (Obj (@LaxArrow_cat C)) a1 b1))
 : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X b0 b1)
≔ Product_pair_grpd (sigma_Fst E)
 (@eq_trans (ArrowPairObservation C) _ _ _ (sigma_Snd E)
  (@arrow_pair_observation_path C a0 a1 b0 b1 p q));
