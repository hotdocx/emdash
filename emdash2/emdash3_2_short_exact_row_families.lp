/*
  A whole native row family with short-exactness evidence at its row views.
  The actual functor owns all base and higher actions. No square field or
  second row/complex grammar is introduced.
*/
require open emdash.emdash3_2_zero_arrow_cone_chain_pairs;
require open emdash.emdash3_2_short_exact_rows;

symbol ShortExactRowFamilyData [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (R : τ (Functor I (@ZeroArrowCone_cat C t T))) : Grpd
≔ @Pi_grpd (Obj I) (λ x : τ (Obj I), (@ComputationalShortExactTriple C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) R x)) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) R x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) R x))
  walking_arrow_tgt) (@zero_arrow_cone_chain_pair C C1 t T (@computational_homology_preadditive C P t PA) (@fapp0 I
  (@ZeroArrowCone_cat C t T) R x))));

symbol ShortExactRowFamily [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) : Grpd
≔ `Σ_ R : τ (Functor I (@ZeroArrowCone_cat C t T)), (@ShortExactRowFamilyData I C C1 P t PA T R);

symbol short_exact_row_family_intro [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (R : τ (Functor I (@ZeroArrowCone_cat C t T))) (short : τ (@ShortExactRowFamilyData I C C1 P t PA T R))
  : τ (@ShortExactRowFamily I C C1 P t PA T)
≔ @Struct_sigma (Functor I (@ZeroArrowCone_cat C t T)) (λ R : τ (Functor I (@ZeroArrowCone_cat C t T)),
  (@ShortExactRowFamilyData I C C1 P t PA T R)) R short;

symbol short_exact_row_family_func [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (F : τ (@ShortExactRowFamily I C C1 P t PA T)) : τ (Functor I (@ZeroArrowCone_cat C t T))
≔ sigma_Fst F;

symbol short_exact_row_family_data [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (F : τ (@ShortExactRowFamily I C C1 P t PA T))
  : τ (@ShortExactRowFamilyData I C C1 P t PA T (@short_exact_row_family_func I C C1 P t PA T F))
≔ sigma_Snd F;

symbol short_exact_row_family_value [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (R : τ (Functor I (@ZeroArrowCone_cat C t T)))
  (short : τ (@ShortExactRowFamilyData I C C1 P t PA T R))
  (x : τ (Obj I))
  : τ (@ComputationalShortExactRow C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0
    I (@ZeroArrowCone_cat C t T) R x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) R x)) walking_arrow_src)
    (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) R x)) walking_arrow_tgt))
≔ @computational_short_exact_row_intro C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) R x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) R x)) walking_arrow_src)
  (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) R x)) walking_arrow_tgt)
    (@zero_arrow_cone_chain_pair C C1 t T (@computational_homology_preadditive C P t PA) (@fapp0 I (@ZeroArrowCone_cat C t
      T) R x)) (short x);

symbol short_exact_row_family_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (F : τ (@ShortExactRowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalShortExactRow C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0
    I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) walking_arrow_src) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) walking_arrow_tgt))
≔ @short_exact_row_family_value I C C1 P t PA T (@short_exact_row_family_func I C C1 P t PA T F)
    (@short_exact_row_family_data I C C1 P t PA T F) x;

/* Existing native Hom action supplies the original row-map views. */

symbol short_exact_row_family_map [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (F : τ (@ShortExactRowFamily I C C1 P t PA T)) [x y : τ (Obj I)] (u : τ (Hom I x y))
  : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    F) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    F) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    F) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) y)) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) y)) walking_arrow_src) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) y)) walking_arrow_tgt)
    (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) (@fapp0 WalkingArrow_cat C
    (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) walking_arrow_src) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) walking_arrow_tgt)
    (@short_exact_row_family_at I C C1 P t PA T F x)) (@computational_short_exact_row_pair C P t PA (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T F) y)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T F) y)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) y)) walking_arrow_tgt)
    (@short_exact_row_family_at I C C1 P t PA T F y)))
≔ @zero_arrow_cone_chain_pair_map C C1 t T (@computational_homology_preadditive C P t PA) (@fapp0 I (@ZeroArrowCone_cat C t
  T) (@short_exact_row_family_func I C C1 P t PA T F) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func
  I C C1 P t PA T F) y) (@fapp1_fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x y u);

symbol short_exact_row_family_transf_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (F G : τ (@ShortExactRowFamily I C C1 P t PA T)) (eta : τ (@Transf I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T F) (@short_exact_row_family_func I C C1 P t PA T G))) (x : τ (Obj I))
  : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    F) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    F) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    F) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T G) x)) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T G) x)) walking_arrow_src) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T G) x)) walking_arrow_tgt)
    (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) (@fapp0 WalkingArrow_cat C
    (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) walking_arrow_src) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F) x)) walking_arrow_tgt)
    (@short_exact_row_family_at I C C1 P t PA T F x)) (@computational_short_exact_row_pair C P t PA (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T G) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T G) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T G) x)) walking_arrow_tgt)
    (@short_exact_row_family_at I C C1 P t PA T G x)))
≔ @zero_arrow_cone_chain_pair_map C C1 t T (@computational_homology_preadditive C P t PA) (@fapp0 I (@ZeroArrowCone_cat C t
  T) (@short_exact_row_family_func I C C1 P t PA T F) x) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func
  I C C1 P t PA T G) x) (@tapp0_fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F)
  (@short_exact_row_family_func I C C1 P t PA T G) x eta);

/*
  Vertex observations use the existing whole postcomposition functors.
  Maps of row families are actual transformations; their higher actions
  remain in the original transfor categories.
*/

symbol short_exact_row_family_observe_func [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (V : τ (Functor (@ZeroArrowCone_cat C t T) C)) (F : τ (@ShortExactRowFamily I C C1 P t PA T))
  : τ (Functor I C)
≔ @comp_cat_fapp0 I (@ZeroArrowCone_cat C t T) C V (@short_exact_row_family_func I C C1 P t PA T F);

symbol short_exact_row_family_observe_transf_func [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (V : τ (Functor (@ZeroArrowCone_cat C t T) C)) (F G : τ (@ShortExactRowFamily I C C1 P t PA T))
  : τ (Functor (@Transf_cat I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F)
    (@short_exact_row_family_func I C C1 P t PA T G)) (@Transf_cat I C (@short_exact_row_family_observe_func I C C1 P t PA T
    V F) (@short_exact_row_family_observe_func I C C1 P t PA T V G)))
≔ @comp_cat_cov_fapp1_func I (@ZeroArrowCone_cat C t T) C V (@short_exact_row_family_func I C C1 P t PA T F)
  (@short_exact_row_family_func I C C1 P t PA T G);

symbol short_exact_row_family_observe_transf [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (V : τ (Functor (@ZeroArrowCone_cat C t T) C)) (F G : τ (@ShortExactRowFamily I C C1 P t PA T))
  (eta : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F)
    (@short_exact_row_family_func I C C1 P t PA T G)))
  : τ (@Transf I C (@short_exact_row_family_observe_func I C C1 P t PA T V F) (@short_exact_row_family_observe_func I C C1 P
    t PA T V G))
≔ @fapp0 (@Transf_cat I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F)
  (@short_exact_row_family_func I C C1 P t PA T G)) (@Transf_cat I C (@short_exact_row_family_observe_func I C C1 P t PA T V
  F) (@short_exact_row_family_observe_func I C C1 P t PA T V G)) (@short_exact_row_family_observe_transf_func I C C1 P t PA
  T V F G) eta;

symbol short_exact_row_family_observe_naturality [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (V : τ (Functor (@ZeroArrowCone_cat C t T) C)) (F G : τ (@ShortExactRowFamily I C C1 P t PA T))
  (eta : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T F)
    (@short_exact_row_family_func I C C1 P t PA T G)))
  [x y : τ (Obj I)] (u : τ (Hom I x y))
  : τ (@= (Hom C (@fapp0 I C (@short_exact_row_family_observe_func I C C1 P t PA T V F) x) (@fapp0 I C
    (@short_exact_row_family_observe_func I C C1 P t PA T V G) y))
      (@comp_fapp0 C _ _ _ (@fapp1_fapp0 I C (@short_exact_row_family_observe_func I C C1 P t PA T V G) x y u) (@tapp0_fapp0
        I C (@short_exact_row_family_observe_func I C C1 P t PA T V F) (@short_exact_row_family_observe_func I C C1 P t PA T
        V G) x (@short_exact_row_family_observe_transf I C C1 P t PA T V F G eta)))
      (@comp_fapp0 C _ _ _ (@tapp0_fapp0 I C (@short_exact_row_family_observe_func I C C1 P t PA T V F)
        (@short_exact_row_family_observe_func I C C1 P t PA T V G) y (@short_exact_row_family_observe_transf I C C1 P t PA T
        V F G eta)) (@fapp1_fapp0 I C (@short_exact_row_family_observe_func I C C1 P t PA T V F) x y u)))
≔ @strict_component_naturality_path I C (@short_exact_row_family_observe_func I C C1 P t PA T V F)
  (@short_exact_row_family_observe_func I C C1 P t PA T V G) (@short_exact_row_family_observe_transf I C C1 P t PA T V F G
  eta) x y u;
