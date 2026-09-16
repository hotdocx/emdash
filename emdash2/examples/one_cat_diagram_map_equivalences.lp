/* Whole reconstruction retains endpoint data and inverse computation. */
require open emdash.emdash3_2_one_cat_diagram_map_equivalences;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)]
 (a : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src)))
 (b : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt)))
 (alpha : τ (Obj (@homdc_square_fibre C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
  WalkingArrow_cat C e walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0
  WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C e walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) a b)))
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src (@one_cat_original_diagram_map C C1 d e a b
  alpha)) ≡ a;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)]
 (a : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src)))
 (b : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt)))
 (alpha : τ (Obj (@homdc_square_fibre C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
  WalkingArrow_cat C e walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0
  WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C e walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) a b)))
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt (@one_cat_original_diagram_map C C1 d e a b
  alpha)) ≡ b;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)] (m : τ
  (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C e d walking_arrow_src (@omega_equiv_along_left_inv (Functor_cat
  WalkingArrow_cat C) d e m (@one_cat_diagram_map_equiv C C1 d e m U V))) ≡ (@omega_equiv_along_left_inv C
  (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_src)
  (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m) U);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)] (m : τ
  (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C e d walking_arrow_tgt (@omega_equiv_along_left_inv (Functor_cat
  WalkingArrow_cat C) d e m (@one_cat_diagram_map_equiv C C1 d e m U V))) ≡ (@omega_equiv_along_left_inv C
  (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt)
  (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m) V);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)] (m : τ
  (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C e d walking_arrow_src (@omega_equiv_along_right_inv (Functor_cat
  WalkingArrow_cat C) d e m (@one_cat_diagram_map_equiv C C1 d e m U V))) ≡ (@omega_equiv_along_left_inv C
  (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_src)
  (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m) U);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)] (m : τ
  (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C e d walking_arrow_tgt (@omega_equiv_along_right_inv (Functor_cat
  WalkingArrow_cat C) d e m (@one_cat_diagram_map_equiv C C1 d e m U V))) ≡ (@omega_equiv_along_left_inv C
  (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt)
  (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m) V);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)] (m : τ
  (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 ⊢ (@omega_equiv_along_left_law (Functor_cat WalkingArrow_cat C) d e m (@one_cat_diagram_map_equiv C C1 d
  e m U V)) : τ (@= (@Transf WalkingArrow_cat C d d) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) d e d
  (@one_cat_diagram_map_inverse C C1 d e m U V) m) (@id (Functor_cat WalkingArrow_cat C) d));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor WalkingArrow_cat C)] (m : τ
  (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 ⊢ (@omega_equiv_along_right_law (Functor_cat WalkingArrow_cat C) d e m (@one_cat_diagram_map_equiv C C1 d
  e m U V)) : τ (@= (@Transf WalkingArrow_cat C e e) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) e d e m
  (@one_cat_diagram_map_inverse C C1 d e m U V)) (@id (Functor_cat WalkingArrow_cat C) e));
