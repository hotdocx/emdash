require open emdash.emdash3_2_one_cat_homology_family_maps;

// Component reconstruction retains both original quotients and the original K action.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (X Y : τ (Functor B C)) (D E : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D)) (k : τ (@Transf B (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ
  (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  E walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C D E m walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T X D h)) (@comp_fapp0 (Functor_cat B C) X Y (@diagram_family_at_func
  B WalkingArrow_cat C E walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T Y E k) a))) (x : τ (Obj
  B)) ⊢ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C
  S t T T0 P Q Y E k)) (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x)) (λ v : τ (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q Y E k)),
  @tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P
  Q Y E k) x v) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) (@homology_adjunction_family_func B C S t T T0 P Q Y E
  k) (@one_cat_homology_family_map_transf B C S C1 t T T0 P Q X Y D E h k a m e)
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) (@homology_adjunction_family_projection_transf B C S t
  T T0 P Q Y E k) (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))
  (@one_cat_homology_family_map_projection_path B C S C1 t T T0 P Q X Y D E h k a m e)) : τ (@= (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q
  Y E k) x)) (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) (@fapp0 B C (@homology_adjunction_family_func B C S
  t T T0 P Q Y E k) x) (@tapp0_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x (@one_cat_homology_family_map_transf B C S C1 t T T0
  P Q X Y D E h k a m e)) (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x (@homology_adjunction_family_projection_transf B C S
  t T T0 P Q X D h))) (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P E) x) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q
  Y E k) x) (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P E) (@homology_adjunction_family_func B C
  S t T T0 P Q Y E k) x (@homology_adjunction_family_projection_transf B C S t T T0 P Q Y E k)) (@tapp0_fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E) x
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (X Y : τ (Functor B C)) (D E : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D)) (k : τ (@Transf B (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ
  (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  E walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C D E m walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T X D h)) (@comp_fapp0 (Functor_cat B C) X Y (@diagram_family_at_func
  B WalkingArrow_cat C E walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T Y E k) a))) (i j : τ (Obj
  B)) ⊢ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C
  S t T T0 P Q Y E k)) (Functor (Hom_cat B i j) (Hom_cat C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P
  D) i) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q Y E k) j))) (λ v : τ (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q Y E k)),
  @tapp1_func B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P
  Q Y E k) i j v) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) (@homology_adjunction_family_func B C S t T T0 P Q Y E
  k) (@one_cat_homology_family_map_transf B C S C1 t T T0 P Q X Y D E h k a m e)
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) (@homology_adjunction_family_projection_transf B C S t
  T T0 P Q Y E k) (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))
  (@one_cat_homology_family_map_projection_path B C S C1 t T T0 P Q X Y D E h k a m e)) : τ (@= (Functor (Hom_cat
  B i j) (Hom_cat C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) i) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) j))) (@tapp1_func B C (@kernel_adjunction_family_func
  B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q Y E k) i j (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q X D h)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) (@one_cat_homology_family_map_transf B C S C1 t T T0 P
  Q X Y D E h k a m e) (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h))) (@tapp1_func B C
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q Y E k) i j
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B
  C S t T P E) (@homology_adjunction_family_func B C S t T T0 P Q Y E k)
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q Y E k) (@kernel_adjunction_family_map_transf B C
  S C1 t T T0 P Q D E m))));
