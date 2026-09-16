/* Map introduction into the existing native zero-cone Hom. */
require open emdash.emdash3_2_zero_arrow_cones;

// Retain the two original components and their native compatibility cell.
symbol zero_cone_native_map [C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
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
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u)))) : τ (Hom
  (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1
  h1))
≔ Struct_sigma u (Struct_sigma v alpha);
