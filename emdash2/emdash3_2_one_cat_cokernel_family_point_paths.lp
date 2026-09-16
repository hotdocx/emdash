/* Observe the original whole cokernel descent through its same scalar mate. */
require open emdash.emdash3_2_kernel_cokernel_adjunction_mates;
require open emdash.emdash3_2_one_cat_adjunction_evaluation_paths;
require open emdash.emdash3_2_one_cat_cokernel_family_descent;
// Use the original whole input, including its original annihilation witness.
symbol one_cat_cokernel_family_descent_point_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)
        Y)))
 (x : τ (Obj B))
 : τ (@= (Hom C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S
  t T0 Q) D) x) (@fapp0 B C Y x)) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D) Y x (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z))
  (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T0 Q (@fapp0 B C Y x) (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) x (@one_cat_cokernel_family_input B C C1 t T T0 D
  Y u z))))
≔ @one_cat_untranspose_evaluation_path B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
  WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 Q) D Y (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z) x;
