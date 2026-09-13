/* Same original additive and whole universal data in the native Abelian package. */
require open emdash.emdash3_2_one_cat_abelian_adjunctions;

// Constructor projection retains the original kernels.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)))
    (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
    (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
    Q))
  ⊢ @one_cat_abelian_adjunction_kernels C C1 Prod t A T0 (@one_cat_abelian_adjunction_intro C C1 Prod t A T0 P Q N) ≡
    P;

// Constructor projection retains the original cokernels.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)))
    (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
    (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
    Q))
  ⊢ @one_cat_abelian_adjunction_cokernels C C1 Prod t A T0 (@one_cat_abelian_adjunction_intro C C1 Prod t A T0 P Q N)
    ≡ Q;

// Constructor projection retains the original normality.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)))
    (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
    (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
    Q))
  ⊢ @one_cat_abelian_adjunction_normality C C1 Prod t A T0 (@one_cat_abelian_adjunction_intro C C1 Prod t A T0 P Q N)
    ≡ N;

// The native H consumer still receives the same K/Q structures.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)))
    (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
    (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
    Q))
  ⊢ @homology_adjunction_family_func Terminal_cat C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
    Prod t A) T0
      (@one_cat_abelian_adjunction_kernels C C1 Prod t A T0 (@one_cat_abelian_adjunction_intro C C1 Prod t A T0 P Q
        N))
      (@one_cat_abelian_adjunction_cokernels C C1 Prod t A T0 (@one_cat_abelian_adjunction_intro C C1 Prod t A T0 P Q
        N))
    ≡ @homology_adjunction_family_func Terminal_cat C (@additive_preadditive C Prod t A) t (@additive_terminal_object
    C Prod t A) T0 P Q;

// Independent selected kernels are not identified by the packaging.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)))
    (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
    (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
    Q)) (P0 : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
    A)))
  ⊢ @one_cat_abelian_adjunction_kernels C C1 Prod t A T0 (@one_cat_abelian_adjunction_intro C C1 Prod t A T0 P Q N) ≡
    P0;

// A normality proof over a different whole comparison cannot be substituted.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)))
    (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
    (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
    Q))
  (b : τ (@Transf (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
    (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)))
  (Nb : τ (@OmegaEquivAlong (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
    (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) b))
  ⊢ @one_cat_abelian_adjunction_intro C C1 Prod t A T0 P Q Nb
    : τ (@OneCatAbelianAdjunctionStructure C C1 Prod t A T0);
