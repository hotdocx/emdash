/* Finite certificate indexing. No native input is existentially reselected. */
require open emdash.emdash3_2_one_cat_native_observed_exactness;
require open emdash.emdash3_2_finite_families;

symbol NativeObservedExactTail [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (n : τ Nat_grpd) (inputs : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) n))
 (first : τ (Obj (@LaxArrow_cat C))) (arrows : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) n)) : Grpd
≔ (@nat_elim
 (λ k : τ Nat_grpd, @Pi_grpd (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) k)
  (λ _ : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) k), @Pi_grpd (Obj (@LaxArrow_cat C))
   (λ _ : τ (Obj (@LaxArrow_cat C)), @Function_grpd (@FiniteFamily (Obj (@LaxArrow_cat C)) k) Grpd_grpd)))
 (λ _ : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) zero), λ _ : τ (Obj (@LaxArrow_cat C)),
  λ _ : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) zero), Unit_grpd)
 (λ k : τ Nat_grpd, λ rec : τ _, λ is : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) (succ k)),
  λ edge : τ (Obj (@LaxArrow_cat C)), λ es : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) (succ k)),
   @Product_grpd
    (@NativeObservedPairExactAt C S C1 t T T0 P Q N (@finite_family_head (Obj (@ZeroArrowCone_cat C t T)) k
  is)
     edge (@finite_family_head (Obj (@LaxArrow_cat C)) k es))
    (rec (@finite_family_tail (Obj (@ZeroArrowCone_cat C t T)) k is) (@finite_family_head (Obj
  (@LaxArrow_cat C)) k es)
     (@finite_family_tail (Obj (@LaxArrow_cat C)) k es))) n) inputs first arrows;

symbol native_observed_exact_tail_nil [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (first : τ (Obj (@LaxArrow_cat C)))
 : τ (@NativeObservedExactTail C S C1 t T T0 P Q N zero (@finite_family_nil (Obj (@ZeroArrowCone_cat C t
  T))) first (@finite_family_nil (Obj (@LaxArrow_cat C))))
≔ tt;

symbol native_observed_exact_tail_cons [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) [n : τ Nat_grpd]
 [X0 : τ (Obj (@ZeroArrowCone_cat C t T))] [inputs : τ (@FiniteFamily (Obj (@ZeroArrowCone_cat C t T)) n)]
 [a0 a1 : τ (Obj (@LaxArrow_cat C))] [arrows : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) n)]
 (E : τ (@NativeObservedPairExactAt C S C1 t T T0 P Q N X0 a0 a1))
 (rest : τ (@NativeObservedExactTail C S C1 t T T0 P Q N n inputs a1 arrows))
 : τ (@NativeObservedExactTail C S C1 t T T0 P Q N (succ n) (@finite_family_cons (Obj (@ZeroArrowCone_cat C
  t T)) n X0 inputs)
   a0 (@finite_family_cons (Obj (@LaxArrow_cat C)) n a1 arrows))
≔ Product_pair_grpd E rest;
