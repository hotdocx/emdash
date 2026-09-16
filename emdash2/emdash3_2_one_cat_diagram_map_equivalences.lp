require open emdash.emdash3_2_one_cat_diagram_map_paths;
require open emdash.emdash3_2_omega_equiv_inverse_square;

// Reconstruct a map at its original diagrams using existing whole shape universality.
symbol one_cat_original_diagram_map [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor
  WalkingArrow_cat C)]
 (a : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src)))
 (b : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt)))
 (alpha : τ (Obj (@homdc_square_fibre C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
  WalkingArrow_cat C e walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0
  WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C e walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) a b)))
 : τ (@Transf WalkingArrow_cat C d e)
≔ (@comp_fapp0 (Functor_cat WalkingArrow_cat C) d (@walking_arrow_func C (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C e
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) e (@one_cat_diagram_reconstruction_to C C1
  e) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) d (@walking_arrow_func C (@fapp0 WalkingArrow_cat C d
  walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@walking_arrow_func C (@fapp0
  WalkingArrow_cat C e walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0
  WalkingArrow_cat C e walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@one_cat_square_diagram_transf C C1 (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
  WalkingArrow_cat C e walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0
  WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C e walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) a b alpha) (@one_cat_diagram_reconstruction_from C C1 d)));

// Derive inverse compatibility from the original transformation, without a new square premise.
symbol one_cat_diagram_map_inverse [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor
  WalkingArrow_cat C)] (m : τ (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 : τ (@Transf WalkingArrow_cat C e d)
≔ (@one_cat_original_diagram_map C C1 e d (@omega_equiv_along_left_inv C (@fapp0 WalkingArrow_cat C d
  walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e
  walking_arrow_src m) U) (@omega_equiv_along_left_inv C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
  (@fapp0 WalkingArrow_cat C e walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt
  m) V) (@path_to_hom (Hom_cat C (@fapp0 WalkingArrow_cat C e walking_arrow_src) (@fapp0 WalkingArrow_cat
  C d walking_arrow_tgt)) _ _ (@omega_equiv_inverse_square_path C (@fapp0 WalkingArrow_cat C d
  walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_src) (@fapp0 WalkingArrow_cat C d
  walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C e
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@tapp0_fapp0 WalkingArrow_cat C d e
  walking_arrow_src m) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m) U V (@eq_sym _ _ _
  (@strict_component_naturality_path WalkingArrow_cat C d e m walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)))));

// Endpoint reflection supplies the law in the original functor category.
symbol one_cat_diagram_map_left_law [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor
  WalkingArrow_cat C)] (m : τ (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 : τ (@= (@Transf WalkingArrow_cat C d d) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) d e d
  (@one_cat_diagram_map_inverse C C1 d e m U V) m) (@id (Functor_cat WalkingArrow_cat C) d))
≔ @one_cat_diagram_map_path C C1 d d (@comp_fapp0 (Functor_cat WalkingArrow_cat C) d e d
  (@one_cat_diagram_map_inverse C C1 d e m U V) m) (@id (Functor_cat WalkingArrow_cat C) d)
 (@omega_equiv_along_left_law C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C
  e walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m) U)
 (@omega_equiv_along_left_law C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C
  e walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m) V);

// Endpoint reflection supplies the law in the original functor category.
symbol one_cat_diagram_map_right_law [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor
  WalkingArrow_cat C)] (m : τ (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 : τ (@= (@Transf WalkingArrow_cat C e e) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) e d e m
  (@one_cat_diagram_map_inverse C C1 d e m U V)) (@id (Functor_cat WalkingArrow_cat C) e))
≔ @one_cat_diagram_map_path C C1 e e (@comp_fapp0 (Functor_cat WalkingArrow_cat C) e d e m
  (@one_cat_diagram_map_inverse C C1 d e m U V)) (@id (Functor_cat WalkingArrow_cat C) e)
 (@omega_equiv_left_as_right_law C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
  WalkingArrow_cat C e walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m) U)
 (@omega_equiv_left_as_right_law C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0
  WalkingArrow_cat C e walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m) V);

// Preserve the original forward transformation and computed inverse components.
symbol one_cat_diagram_map_equiv [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [d e : τ (Functor
  WalkingArrow_cat C)] (m : τ (@Transf WalkingArrow_cat C d e))
 (U : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e
  walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src m)))
 (V : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e
  walking_arrow_tgt) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt m)))
 : τ (@OmegaEquivAlong (Functor_cat WalkingArrow_cat C) d e m)
≔ @omega_equiv_along_intro (Functor_cat WalkingArrow_cat C) d e m (@one_cat_diagram_map_inverse C C1 d e m
  U V) (@one_cat_diagram_map_inverse C C1 d e m U V)
 (@one_cat_diagram_map_left_law C C1 d e m U V)
 (@one_cat_diagram_map_right_law C C1 d e m U V);
