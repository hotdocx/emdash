/* Selected inverse components and both laws of the original native map. */
require open emdash.emdash3_2_one_cat_zero_cone_map_equivalences;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj
  C t T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0) (@omega_equiv_along_left_inv (@ZeroArrowCone_cat
  C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m
  (@one_cat_zero_cone_map_equiv C C1 t T a0 a1 d0 d1 h0 h1 m U V))) ≡ (@omega_equiv_along_left_inv C a0
  a1 (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) U);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@omega_equiv_along_left_inv (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0
  h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_equiv C C1 t T a0 a1 d0 d1 h0 h1 m
  U V))) ≡ (@omega_equiv_along_left_inv (Functor_cat WalkingArrow_cat C) d0 d1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) V);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj
  C t T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0) (@omega_equiv_along_right_inv
  (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1)
  m (@one_cat_zero_cone_map_equiv C C1 t T a0 a1 d0 d1 h0 h1 m U V))) ≡ (@omega_equiv_along_left_inv C
  a0 a1 (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) U);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@omega_equiv_along_right_inv (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0
  h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_equiv C C1 t T a0 a1 d0 d1 h0 h1 m
  U V))) ≡ (@omega_equiv_along_left_inv (Functor_cat WalkingArrow_cat C) d0 d1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) V);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t))
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
 ⊢ (@omega_equiv_along_left_law (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_equiv C C1 t T a0 a1 d0 d1 h0 h1 m U
  V)) : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a0 d0 h0)) (@comp_fapp0 (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C
  t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U V) m) (@id (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0)));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t))
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
 ⊢ (@omega_equiv_along_right_law (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_equiv C C1 t T a0 a1 d0 d1 h0 h1 m U
  V)) : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a1 d1 h1)
  (@zero_arrow_cone_obj C t T a1 d1 h1)) (@comp_fapp0 (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C
  t T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m
  (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U V)) (@id (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T a1 d1 h1)));
