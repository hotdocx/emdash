require open emdash.emdash3_2_one_cat_zero_cone_map_paths;
require open emdash.emdash3_2_omega_equiv_inverse_square;

// The inverse uses the existing component inverses and whole naturality.
symbol one_cat_zero_cone_map_inverse [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
 : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t T
  a0 d0 h0))
≔ let u : τ (Hom C a0 a1) ≔ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
  T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) in
 let v : τ (@Transf WalkingArrow_cat C d0 d1) ≔ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m) in
 let iu : τ (Hom C a1 a0) ≔ @omega_equiv_along_left_inv C a0 a1 u U in
 let iv : τ (@Transf WalkingArrow_cat C d1 d0) ≔ @omega_equiv_along_left_inv (Functor_cat
  WalkingArrow_cat C) d0 d1 v V in
 @zero_cone_native_map C t T a1 a0 d1 d0 h1 h0 iu iv
   (@path_to_hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a1) d0) _ _
     (@omega_equiv_inverse_square_path (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) (@fapp0 C (Functor_cat WalkingArrow_cat
  C) (@terminal_arrow_diagram_func C t T) a1) d0 d1 h0 h1
       (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u) v
       (@omega_equiv_along_fapp1_fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) a0 a1 u U) V
       (@zero_arrow_cone_map_naturality C C1 t T (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m)));

// Projected inverse laws determine the original native composite.
symbol one_cat_zero_cone_map_left_law [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
 : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a0 d0 h0)) (@comp_fapp0 (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U V) m) (@id (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0)))
≔ @one_cat_zero_cone_map_path C C1 t T a0 a0 d0 d0 h0 h0
 (@comp_fapp0 (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0) (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1
  h0 h1 m U V) m) (@id (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0))
 (@eq_trans _ _ _ _
   (@fapp1_comp_path (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U V) m)
   (@omega_equiv_along_left_law C a0 a1 (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1 h1) m) U))
 (@eq_trans _ _ _ _
   (@fapp1_comp_path (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0) (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1
  h0 h1 m U V) m)
   (@omega_equiv_along_left_law (Functor_cat WalkingArrow_cat C) d0 d1 (@fapp1_fapp0 (@ZeroArrowCone_cat
  C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C
  t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) V));

// Projected inverse laws determine the original native composite.
symbol one_cat_zero_cone_map_right_law [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
 : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t
  T a1 d1 h1)) (@comp_fapp0 (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a1 d1 h1)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m
  (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U V)) (@id (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T a1 d1 h1)))
≔ @one_cat_zero_cone_map_path C C1 t T a1 a1 d1 d1 h1 h1
 (@comp_fapp0 (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0
  d1 h0 h1 m U V)) (@id (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a1 d1 h1))
 (@eq_trans _ _ _ _
   (@fapp1_comp_path (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1 h1) m (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U V))
   (@omega_equiv_left_as_right_law C a0 a1 (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1 h1) m) U))
 (@eq_trans _ _ _ _
   (@fapp1_comp_path (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a1 d1 h1) (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0
  d1 h0 h1 m U V))
   (@omega_equiv_left_as_right_law (Functor_cat WalkingArrow_cat C) d0 d1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) V));

// Fixed-forward equivalence retains the original native map and computed inverse.
symbol one_cat_zero_cone_map_equiv [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
 : τ (@OmegaEquivAlong (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m)
≔ @omega_equiv_along_intro (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U
  V) (@one_cat_zero_cone_map_inverse C C1 t T a0 a1 d0 d1 h0 h1 m U V)
 (@one_cat_zero_cone_map_left_law C C1 t T a0 a1 d0 d1 h0 h1 m U V)
 (@one_cat_zero_cone_map_right_law C C1 t T a0 a1 d0 d1 h0 h1 m U V);
