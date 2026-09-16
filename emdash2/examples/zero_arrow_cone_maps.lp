/* Both whole projection functors retain the supplied nonidentity components. */
require open emdash.emdash3_2_zero_arrow_cone_maps;

assert [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a0 a1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a0) d0)]
 [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a1) d1)]
 (u : τ (Hom C a0 a1)) (v : τ (@Transf WalkingArrow_cat C d0 d1))
 (alpha : τ (Hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 v h0) (@comp_fapp0
  (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t
  T) a0) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u))))  ⊢ (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_cone_native_map C t T a0 a1 d0 d1 h0 h1 u v alpha)) ≡ u;

assert [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a0 a1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a0) d0)]
 [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a1) d1)]
 (u : τ (Hom C a0 a1)) (v : τ (@Transf WalkingArrow_cat C d0 d1))
 (alpha : τ (Hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 v h0) (@comp_fapp0
  (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t
  T) a0) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u))))  ⊢ (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_cone_native_map C t
  T a0 a1
  d0 d1 h0 h1 u v alpha)) ≡ v;
