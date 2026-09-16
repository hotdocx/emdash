/* Transport preserves canonical exactness at the target native input. */
require open emdash.emdash3_2_one_cat_categorical_exactness_points;

assert [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 [X Y : τ (Obj (@ZeroArrowCone_cat C t T))] (m : τ (Hom (@ZeroArrowCone_cat C t T) X Y)) (M : τ
  (@OmegaEquivAlong (@ZeroArrowCone_cat C t T) X Y m))
 (E : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N X))  ⊢ (@one_cat_native_exactness_transport C S C1 t T T0 P Q N X Y m M E) : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N Y);
