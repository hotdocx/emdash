require open emdash.emdash3_2_one_cat_native_exact_diagrams;

// Structural assembly preserves the original head certificate.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) [n : τ Nat_grpd]
 [X0 : τ (Obj (@ZeroArrowCone_cat C t T))] [inputs : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) n)]
 [a0 a1 : τ (Obj (@LaxArrow_cat C))] [arrows : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) n)]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X0 a0 a1))
 (rest : τ (@NativeObservedExactTail C S C1 t T T0 P Q N n inputs a1 arrows)) ⊢ sigma_Fst
  (@native_observed_exact_tail_cons C S C1 t T T0 P Q N n X0 inputs a0 a1 arrows E rest) ≡ E;

// The actual tail is retained without reconstructing any witness.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) [n : τ Nat_grpd]
 [X0 : τ (Obj (@ZeroArrowCone_cat C t T))] [inputs : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) n)]
 [a0 a1 : τ (Obj (@LaxArrow_cat C))] [arrows : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) n)]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X0 a0 a1))
 (rest : τ (@NativeObservedExactTail C S C1 t T T0 P Q N n inputs a1 arrows)) ⊢ sigma_Snd
  (@native_observed_exact_tail_cons C S C1 t T T0 P Q N n X0 inputs a0 a1 arrows E rest) ≡ rest;

// One retained native input is required for each adjacent arrow pair.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) [n : τ Nat_grpd]
 [X0 : τ (Obj (@ZeroArrowCone_cat C t T))] [inputs : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) n)]
 [a0 a1 : τ (Obj (@LaxArrow_cat C))] [arrows : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) n)]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X0 a0 a1))
 (rest : τ (@NativeObservedExactTail C S C1 t T T0 P Q N n inputs a1 arrows)) ⊢
  (@native_observed_exact_tail_cons C S C1 t T T0 P Q N n X0 inputs a0 a1 arrows E rest) : τ
  (@NativeObservedExactTail C S C1 t T T0 P Q N (succ n) (@finite_family_cons (Obj (@ZeroArrowCone_cat C t
  T)) n X0 inputs) a0 (@finite_family_cons (Obj (@LaxArrow_cat C)) n a1 arrows));

// A different head input is not certified by this constructor.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) [n : τ Nat_grpd]
 [X0 : τ (Obj (@ZeroArrowCone_cat C t T))] [inputs : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) n)]
 [a0 a1 : τ (Obj (@LaxArrow_cat C))] [arrows : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) n)]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X0 a0 a1))
 (rest : τ (@NativeObservedExactTail C S C1 t T T0 P Q N n inputs a1 arrows)) (Y : τ (Obj
  (@ZeroArrowCone_cat C t T))) ⊢ (@native_observed_exact_tail_cons C S C1 t T T0 P Q N n X0 inputs a0 a1
  arrows E rest) : τ (@NativeObservedExactTail C S C1 t T T0 P Q N (succ n) (@finite_family_cons (Obj
  (@ZeroArrowCone_cat C t T)) n Y inputs) a0 (@finite_family_cons (Obj (@LaxArrow_cat C)) n a1 arrows));
