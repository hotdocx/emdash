/* Whole postcomposition of zero through the original initial-family uniqueness. */
require open emdash.emdash3_2_one_cat_kernel_pullback_lifts;

symbol one_cat_zero_family_postcompose_path [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X A Y : τ (Functor B C)) (u : τ (@Transf B C A Y))
  : τ (@= (@Transf B C X Y)
      (@comp_fapp0 (Functor_cat B C) X A Y u (@zero_arrow_family_zero_transf B C t T T0 X A))
      (@zero_arrow_family_zero_transf B C t T T0 X Y))
≔ @eq_ap (@Transf B C (@Const_func B C t) Y) (@Transf B C X Y)
    (λ j : τ (@Transf B C (@Const_func B C t) Y),
      @comp_fapp0 (Functor_cat B C) X (@Const_func B C t) Y j
        (@diagram_family_transf B WalkingArrow_cat C
          (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
          walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@comp_fapp0 (Functor_cat B C) (@Const_func B C t) A Y u
      (@diagram_family_transf B WalkingArrow_cat C
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) A)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@diagram_family_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_initial_family_arrow_path B C C1 t T0 Y
      (@comp_fapp0 (Functor_cat B C) (@Const_func B C t) A Y u
        (@diagram_family_transf B WalkingArrow_cat C
          (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) A)
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)));
