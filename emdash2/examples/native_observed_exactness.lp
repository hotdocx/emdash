require open emdash.emdash3_2_one_cat_native_observed_exactness;

// Complete observation transport keeps the fixed native input.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (X Y : τ (Obj (@ZeroArrowCone_cat C t T)))
 [a0 a1 b0 b1 : τ (Obj (@LaxArrow_cat C))]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X a0 a1))
 (p : τ (@= (Obj (@LaxArrow_cat C)) a0 b0))
 (q : τ (@= (Obj (@LaxArrow_cat C)) a1 b1)) ⊢ (@native_observed_pair_exact_transport C S C1 t T T0 P Q N X a0 a1 b0 b1 E p q) : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X b0 b1);

// The original canonical witness is judgmentally unchanged, including both inverse slots.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (X Y : τ (Obj (@ZeroArrowCone_cat C t T)))
 [a0 a1 b0 b1 : τ (Obj (@LaxArrow_cat C))]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X a0 a1))
 (p : τ (@= (Obj (@LaxArrow_cat C)) a0 b0))
 (q : τ (@= (Obj (@LaxArrow_cat C)) a1 b1)) ⊢ sigma_Fst (@native_observed_pair_exact_transport C S C1 t T T0 P Q N X a0 a1 b0 b1 E p q) ≡ sigma_Fst E;

// Only the observation path is extended.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (X Y : τ (Obj (@ZeroArrowCone_cat C t T)))
 [a0 a1 b0 b1 : τ (Obj (@LaxArrow_cat C))]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X a0 a1))
 (p : τ (@= (Obj (@LaxArrow_cat C)) a0 b0))
 (q : τ (@= (Obj (@LaxArrow_cat C)) a1 b1)) ⊢ sigma_Snd (@native_observed_pair_exact_transport C S C1 t T T0 P Q N X a0 a1 b0 b1 E p q) ≡ (@eq_trans (ArrowPairObservation C) _ _ _ (sigma_Snd E) (@arrow_pair_observation_path C a0 a1 b0 b1 p q));

// Observation agreement alone must not certify a different native input.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (X Y : τ (Obj (@ZeroArrowCone_cat C t T)))
 [a0 a1 b0 b1 : τ (Obj (@LaxArrow_cat C))]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X a0 a1))
 (p : τ (@= (Obj (@LaxArrow_cat C)) a0 b0))
 (q : τ (@= (Obj (@LaxArrow_cat C)) a1 b1)) ⊢ (@native_observed_pair_exact_transport C S C1 t T T0 P Q N X a0 a1 b0 b1 E p q) : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N Y b0 b1);
