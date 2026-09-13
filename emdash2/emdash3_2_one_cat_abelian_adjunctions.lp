/* Whole Abelian adjunction data over the original additive capability. */
require open emdash.emdash3_2_one_cat_adjunction_normality;
require open emdash.emdash3_2_additive_categories;

// The additive capability retains its whole binary product and terminal object.
// P/Q and fixed-a normality are additional coherent structure, not inferred data.
symbol OneCatAbelianAdjunctionStructure [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) : Grpd
≔ `Σ_ P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
      (@additive_terminal_object C Prod t A)),
    `Σ_ Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0),
      @OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
        (@additive_terminal_object C Prod t A) T0 P Q;

symbol one_cat_abelian_adjunction_intro [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
    (@additive_terminal_object C Prod t A)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
    (@additive_terminal_object C Prod t A) T0 P Q))
  : τ (@OneCatAbelianAdjunctionStructure C C1 Prod t A T0)
≔ Struct_sigma P (Struct_sigma Q N);

// Original whole kernel structure, without deriving or selecting any W.
symbol one_cat_abelian_adjunction_kernels [C : Cat]
  [C1 : τ (IsNCat (cat_succ cat_zero) C)]
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  [A : τ (@AdditiveCategory C Prod t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (V : τ (@OneCatAbelianAdjunctionStructure C C1 Prod t A T0))
  : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
      (@additive_terminal_object C Prod t A))
≔ sigma_Fst V;

// Original whole cokernel structure, independent of ordinary V-indexed factors.
symbol one_cat_abelian_adjunction_cokernels [C : Cat]
  [C1 : τ (IsNCat (cat_succ cat_zero) C)]
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  [A : τ (@AdditiveCategory C Prod t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (V : τ (@OneCatAbelianAdjunctionStructure C C1 Prod t A T0))
  : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)
≔ sigma_Fst (sigma_Snd V);

// Normality is indexed by the actual comparison of these same P/Q projections.
symbol one_cat_abelian_adjunction_normality [C : Cat]
  [C1 : τ (IsNCat (cat_succ cat_zero) C)]
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  [A : τ (@AdditiveCategory C Prod t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (V : τ (@OneCatAbelianAdjunctionStructure C C1 Prod t A T0))
  : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
      (@additive_terminal_object C Prod t A) T0
      (@one_cat_abelian_adjunction_kernels C C1 Prod t A T0 V)
      (@one_cat_abelian_adjunction_cokernels C C1 Prod t A T0 V))
≔ sigma_Snd (sigma_Snd V);
