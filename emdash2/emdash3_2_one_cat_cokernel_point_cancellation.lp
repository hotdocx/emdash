/* Point cancellation through the original whole adjunction and diagram reconstruction. */
require open emdash.emdash3_2_one_cat_diagram_map_paths;
require open emdash.emdash3_2_kernel_cokernel_adjunction_observations;

// Existing diagram faithfulness and terminal uniqueness reflect the target component.
symbol one_cat_initial_test_reflect_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (Y : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
 (h k : τ (@Transf WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func
  C t T0) Y)))
 (p : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Y) (@tapp0_fapp0 WalkingArrow_cat C d (@fapp0
  C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) walking_arrow_tgt h) (@tapp0_fapp0
  WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
  walking_arrow_tgt k)))
 : τ (@= (@Transf WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C
  t T0) Y)) h k)
≔ @one_cat_diagram_map_path C C1 d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t
  T0) Y) h k
  (@eq_trans _ _ _ _ (@terminal_unique_path C t T (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0
  WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
  walking_arrow_src h))
    (@eq_sym _ _ _ (@terminal_unique_path C t T (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0
  WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
  walking_arrow_src k)))) p;

// Apply the same colift functor after reflecting the native cocone components.
symbol one_cat_cokernel_projection_reflect_path [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (Q : τ (@CokernelAdjunctionStructure C S t T0)) (Y : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
 (u v : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) d) Y))
 (p : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Y)
   (@initial_arrow_test_outgoing C t T0 Y d (@fapp0 _ _ (@cokernel_adjunction_uncolift_func C S t T0 Q Y d) u))
   (@initial_arrow_test_outgoing C t T0 Y d (@fapp0 _ _ (@cokernel_adjunction_uncolift_func C S t T0 Q Y d)
  v))))
 : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) d) Y) u v)
≔ @eq_ap (@Transf WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C
  t T0) Y))
   (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) d) Y)
   (λ h : τ (@Transf WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) Y)), @fapp0 _ _ (@cokernel_adjunction_colift_func C S t T0 Q Y d) h)
   _ _ (@one_cat_initial_test_reflect_path C C1 t T T0 Y d
     (@fapp0 _ _ (@cokernel_adjunction_uncolift_func C S t T0 Q Y d) u)
     (@fapp0 _ _ (@cokernel_adjunction_uncolift_func C S t T0 Q Y d) v) p);

// Equality after the original quotient is reflected by its native adjunction mate.
symbol one_cat_cokernel_quotient_reflect_path [C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (Q : τ (@CokernelAdjunctionStructure C S t T0)) (Y : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
 (u v : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) d) Y))
 (p : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Y) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C
  d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) d) Y u
  (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q) d (@cokernel_adjunction_projection C S t T0 Q)))
  (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) d) Y v (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q) d
  (@cokernel_adjunction_projection C S t T0 Q)))))
 : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) d) Y) u v)
≔ @one_cat_cokernel_projection_reflect_path C S C1 t T T0 Q Y d u v
   (@eq_trans _ _ _ _ (@cokernel_adjunction_uncolift_target_path C S t T0 Q Y d u)
      (@eq_trans _ _ _ _ p (@eq_sym _ _ _ (@cokernel_adjunction_uncolift_target_path C S t T0 Q Y d v))));
