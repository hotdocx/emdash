/* Original raw fields are observations of the same nonidentity native map. */
require open emdash.emdash3_2_zero_arrow_cone_chain_pairs;

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A0 A1 : τ (Obj C))
  (d0 d1 : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d0))
  (h1 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A1) d1))
  (a : τ (Hom C A0 A1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (theta : τ (Obj (@homdc_fibre C (Functor_cat WalkingArrow_cat C)
    (@represented_comma_prof C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
    A0 A1 d0 d1 h0 h1 a b))) ⊢
  @computational_chain_pair_map_next C S A0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt)
      A1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt)
    (@zero_arrow_cone_chain_pair C C1 t T S (@zero_arrow_cone_obj C t T A0 d0 h0)) (@zero_arrow_cone_chain_pair C C1 t T S (@zero_arrow_cone_obj C t T A1 d1 h1)) (@zero_arrow_cone_chain_pair_map C C1 t T S (@zero_arrow_cone_obj C t T A0 d0 h0) (@zero_arrow_cone_obj C t T A1 d1 h1) (Struct_sigma a (Struct_sigma b theta)))
  ≡ a;

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A0 A1 : τ (Obj C))
  (d0 d1 : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d0))
  (h1 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A1) d1))
  (a : τ (Hom C A0 A1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (theta : τ (Obj (@homdc_fibre C (Functor_cat WalkingArrow_cat C)
    (@represented_comma_prof C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
    A0 A1 d0 d1 h0 h1 a b))) ⊢
  @computational_chain_pair_map_middle C S A0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt)
      A1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt)
    (@zero_arrow_cone_chain_pair C C1 t T S (@zero_arrow_cone_obj C t T A0 d0 h0)) (@zero_arrow_cone_chain_pair C C1 t T S (@zero_arrow_cone_obj C t T A1 d1 h1)) (@zero_arrow_cone_chain_pair_map C C1 t T S (@zero_arrow_cone_obj C t T A0 d0 h0) (@zero_arrow_cone_obj C t T A1 d1 h1) (Struct_sigma a (Struct_sigma b theta)))
  ≡ @tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src b;

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A0 A1 : τ (Obj C))
  (d0 d1 : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d0))
  (h1 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A1) d1))
  (a : τ (Hom C A0 A1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (theta : τ (Obj (@homdc_fibre C (Functor_cat WalkingArrow_cat C)
    (@represented_comma_prof C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
    A0 A1 d0 d1 h0 h1 a b))) ⊢
  @computational_chain_pair_map_prev C S A0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt)
      A1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt)
    (@zero_arrow_cone_chain_pair C C1 t T S (@zero_arrow_cone_obj C t T A0 d0 h0)) (@zero_arrow_cone_chain_pair C C1 t T S (@zero_arrow_cone_obj C t T A1 d1 h1)) (@zero_arrow_cone_chain_pair_map C C1 t T S (@zero_arrow_cone_obj C t T A0 d0 h0) (@zero_arrow_cone_obj C t T A1 d1 h1) (Struct_sigma a (Struct_sigma b theta)))
  ≡ @tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_tgt b;

// Object-set truncation alone is not the required local-Hom profile.
assertnot (C : Cat) (objects_set : τ (IsSetGrpd (Obj C))) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) ⊢
  @zero_arrow_cone_universal_transf C objects_set t T
  : τ (@Transf (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
      (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@zero_arrow_cone_first_func C t T))
      (@zero_arrow_cone_diagram_func C t T));
