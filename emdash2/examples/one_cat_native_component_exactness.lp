/* Transport the original canonical exactness using component equivalences.
   No new full-input equivalence or target-exactness premise is supplied. */
require open emdash.emdash3_2_one_cat_categorical_exactness_points;
require open emdash.emdash3_2_one_cat_zero_cone_map_equivalences;

symbol native_component_equivalence_exactness [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ
  cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))

 [a0 a1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d0)]
 [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a1) d1)]
 (m : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1 h1)))
 (U : τ (@OmegaEquivAlong C a0 a1 (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1 h1) m)))
 (V : τ (@OmegaEquivAlong (Functor_cat WalkingArrow_cat C) d0 d1 (@fapp1_fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T
  a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m)))
 (E : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N (@zero_arrow_cone_obj C t T a0 d0 h0)))
 : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N (@zero_arrow_cone_obj C t T a1 d1 h1))
≔ @one_cat_native_exactness_transport C S C1 t T T0 P Q N (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_equiv C C1 t T a0 a1 d0 d1 h0 h1 m U
  V) E;
