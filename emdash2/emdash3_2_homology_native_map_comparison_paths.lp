/* Internal proof bridge: compatibility at cycles is discharged by diagram action.
   Whole H maps and the original comparisons remain the program data. */
require open emdash.emdash3_2_homology_family_map_point_observations;
require open emdash.emdash3_2_one_cat_quotient_comparison_paths;

symbol homology_family_native_map_comparison_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject
  (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (X Y
  : τ
  (Functor B C)) (D E : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T)
  X) D)) (k : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@sym_transf_tapp0_transf
  B WalkingArrow_cat C D E m walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T X D h))
  (@comp_fapp0
  (Functor_cat B C) X Y (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T Y E k) a))) (x : τ (Obj B))
 (N0 N1 : τ (Obj (@ZeroArrowCone_cat C t T)))
 (n0 : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_family_point_input B C t T X D h x) N0)) (n1 : τ
  (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_family_point_input B C t T Y E k x) N1))
 (v : τ (Hom (@ZeroArrowCone_cat C t T) N0 N1))
 (cycle_comparison : τ (@= (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T)) N1)) (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func B
  C S t T P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N0) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C
  t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N0 N1 v) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T)
  C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C
  t T)) (@zero_arrow_family_point_input B C t T X D h x) N0 n0)) (@comp_fapp0 C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@kernel_adjunction_family_func B C S t T
  P E) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T)
  C S t T P (@zero_arrow_cone_diagram_func C t T)) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) (@zero_arrow_family_point_input B C t T Y E k x) N1 n1) (@tapp0_fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E) x
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)))))
 : τ (@= (Hom C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1))
  (@comp_fapp0 C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N0) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1)
  (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  N0 N1 v) (@comp_fapp0 C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input B C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N0) (@fapp1_fapp0 (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input B C t
  T X D h x) N0 n0) (@homology_family_global_point_map B C S C1 t T T0 P Q X D h x))) (@comp_fapp0 C
  (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1) (@comp_fapp0 C (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input B C t T Y
  E k x)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P
  Q) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T
  T0 P Q) (@zero_arrow_family_point_input B C t T Y E k x) N1 n1) (@homology_family_global_point_map B C S
  C1 t T T0 P Q Y E k x)) (@tapp0_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x (@one_cat_homology_family_map_transf B C S
  C1 t T T0 P Q X Y D E h k a m e))))
≔ @homology_family_point_quotient_reflect_path B C S C1 t T T0 P Q X D h x (@fapp0 (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1) (@comp_fapp0 C (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N0) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N0 N1 v) (@comp_fapp0 C (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input B C t T X
  D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P
  Q) N0) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T
  T0 P Q) (@zero_arrow_family_point_input B C t T X D h x) N0 n0) (@homology_family_global_point_map B C S
  C1 t T T0 P Q X D h x))) (@comp_fapp0 C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X
  D h) x) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1)
  (@comp_fapp0 C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input B C t T Y E k x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input B C t
  T Y E k x) N1 n1) (@homology_family_global_point_map B C S C1 t T T0 P Q Y E k x)) (@tapp0_fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) (@homology_adjunction_family_func B C S t T T0
  P Q Y E k) x (@one_cat_homology_family_map_transf B C S C1 t T T0 P Q X Y D E h k a m e)))
 (@comparison_after_quotient_path C C1 (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x)
  (@fapp0 B C (@kernel_adjunction_family_func B C S t T P E) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N0) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T)
  C S t T P (@zero_arrow_cone_diagram_func C t T)) N1) (@fapp0 B C (@homology_adjunction_family_func B C S
  t T T0 P Q X D h) x) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N0) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1)
  (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S
  t T T0 P Q X D h) x (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h))
  (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P E) (@homology_adjunction_family_func B C S
  t T T0 P Q Y E k) x (@homology_adjunction_family_projection_transf B C S t T T0 P Q Y E k))
  (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C
  S t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0
  P Q) N0 (@homology_adjunction_family_projection_transf (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N1
  (@homology_adjunction_family_projection_transf (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@tapp0_fapp0 B C (@homology_adjunction_family_func B C S
  t T T0 P Q X D h) (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x
  (@one_cat_homology_family_map_transf B C S C1 t T T0 P Q X Y D E h k a m e)) (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N0 N1 v)
  (@comp_fapp0 C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input B C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) N0) (@fapp1_fapp0 (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input B C t
  T X D h x) N0 n0) (@homology_family_global_point_map B C S C1 t T T0 P Q X D h x)) (@comp_fapp0 C
  (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x) (@fapp0 (@ZeroArrowCone_cat C t
  T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_family_point_input B C t
  T Y E k x)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T
  T0 P Q) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1
  t T T0 P Q) (@zero_arrow_family_point_input B C t T Y E k x) N1 n1) (@homology_family_global_point_map B
  C S C1 t T T0 P Q Y E k x)) (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P E) x (@kernel_adjunction_family_map_transf B C S C1 t T T0 P
  Q D E m)) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N0 N1 v) (@fapp1_fapp0 (@ZeroArrowCone_cat C t
  T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func
  C t T)) (@zero_arrow_family_point_input B C t T X D h x) N0 n0) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T)
  C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C
  t T)) (@zero_arrow_family_point_input B C t T Y E k x) N1 n1)
  (@homology_family_native_comparison_quotient_path B C S C1 t T T0 P Q X D h x N0 n0)
  (@homology_family_native_comparison_quotient_path B C S C1 t T T0 P Q Y E k x N1 n1)
  (@homology_family_map_projection_at_path B C S C1 t T T0 P Q X Y D E h k a m e x)
  (@strict_component_naturality_path (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T))
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@homology_adjunction_family_projection_transf (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) N0 N1 v) cycle_comparison);
