/* Original K action transports the actual diagram comparison to cycles. */
require open emdash.emdash3_2_kernel_family_map_point_views;
require open emdash.emdash3_2_zero_arrow_family_point_inputs;
require open emdash.emdash3_2_one_cat_homology_family_maps;

symbol homology_native_comparison_cycle_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
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
 (diagram_comparison : τ (@= (@Transf WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T X D h
  x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
  t T) N1)) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T X D h
  x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
  t T) N0) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) N0 N1 v) (@fapp1_fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_family_point_input B C t T X D h x) N0 n0)) (@comp_fapp0 (Functor_cat WalkingArrow_cat C)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@zero_arrow_family_point_input B C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T Y E k
  x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
  t T) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T Y E k x) N1 n1)
  (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) D E x m))))
 : τ (@= (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 (@ZeroArrowCone_cat
  C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
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
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))))
≔ (@eq_trans _ _ _ _ (@eq_ap (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N0) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T)) N1)) (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T
  P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T)
  C S t T P (@zero_arrow_cone_diagram_func C t T)) N1)) (λ cell : τ (Hom C (@fapp0 (@ZeroArrowCone_cat C t
  T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func
  C t T)) N0) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t
  T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N1)), (@comp_fapp0 C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N0) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T)
  C S t T P (@zero_arrow_cone_diagram_func C t T)) N1) cell (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) (@zero_arrow_family_point_input B C t T X D h x) N0 n0))) _ _ (@native_kernel_map_diagram_path C S
  C1 t T P N0 N1 v)) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t
  T P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t
  T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N0)) (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N1)) (λ cell : τ (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T)) N0)), (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func
  B C S t T P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N0) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T)) N1) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) N0) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) N0 N1 v)) cell)) _ _
  (@native_kernel_map_diagram_path C S C1 t T P (@zero_arrow_family_point_input B C t T X D h x) N0 n0))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@fapp1_comp_path (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T X D h x)) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) N0)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) N0 N1 v) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T X D h
  x) N0 n0))) (@eq_trans _ _ _ _ (@eq_ap (@Transf WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B
  C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) N1)) (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T
  P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T)
  C S t T P (@zero_arrow_cone_diagram_func C t T)) N1)) (λ cell : τ (@Transf WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_family_point_input B C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) N1)), (@fapp1_fapp0 (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B
  C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) N1) cell)) _ _ diagram_comparison) (@eq_trans _ _ _ _
  (@fapp1_comp_path (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_family_point_input B C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T Y E k
  x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
  t T) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T Y E k x) N1 n1)
  (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) D E x m)) (@eq_trans _ _ _ _ (@eq_ap (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P E) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N1)) (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T)) N1)) (λ cell : τ (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P E) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N1)), (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P E) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N1) cell (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@zero_arrow_family_point_input B C t T X D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_family_point_input B C t T Y E k
  x)) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) D E x m)))) _ _ (@eq_sym _ _ _
  (@native_kernel_map_diagram_path C S C1 t T P (@zero_arrow_family_point_input B C t T Y E k x) N1 n1)))
  (@eq_ap (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P E) x)) (Hom C (@fapp0 B C (@kernel_adjunction_family_func B
  C S t T P D) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) N1)) (λ cell : τ (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@kernel_adjunction_family_func B C S t T
  P E) x)), (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P E) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) N1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C
  t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input B C t T Y E k x)
  N1 n1) cell)) _ _ (@eq_sym _ _ _ (@kernel_family_map_at_path B C S C1 t T T0 P Q D E m x)))))))));
