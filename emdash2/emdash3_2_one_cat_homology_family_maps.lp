require open emdash.emdash3_2_one_cat_arrow_family_maps;
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_maps;
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;
require open emdash.emdash3_2_one_cat_homology_cover_maps;

// Original kernel action and boundary reconstruction give the whole boundary-map relation.
symbol one_cat_homology_family_boundary_map_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (X Y : τ
  (Functor B C)) (D E : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  X) D)) (k : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C D E m walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T X D h)) (@comp_fapp0
  (Functor_cat B C) X Y (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T Y E k) a)))
 : τ (@= (@Transf B C X (@kernel_adjunction_family_func B C S t T P E)) (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E)
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)
  (@kernel_adjunction_family_boundary_transf B C S t T P X D h)) (@comp_fapp0 (Functor_cat B C) X Y
  (@kernel_adjunction_family_func B C S t T P E) (@kernel_adjunction_family_boundary_transf B C S t T P Y E k) a))
≔ @one_cat_kernel_family_inclusion_reflect_path B C S C1 t T T0 P X E (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E)
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)
  (@kernel_adjunction_family_boundary_transf B C S t T P X D h)) (@comp_fapp0 (Functor_cat B C) X Y
  (@kernel_adjunction_family_func B C S t T P E) (@kernel_adjunction_family_boundary_transf B C S t T P Y E k) a)
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P E) (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P E)
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)
  (@kernel_adjunction_family_boundary_transf B C S t T P X D h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)) (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (λ v : τ
  (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D)
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) v (@kernel_adjunction_family_boundary_transf
  B C S t T P X D h))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P E) (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P E)
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C D E m walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D))
  (@one_cat_kernel_family_map_inclusion_path B C S C1 t T T0 P Q D E m)) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C D E m walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T
  P X D h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (λ v : τ
  (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B
  C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C E walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C D E m walking_arrow_src)
  v)) (@comp_fapp0 (Functor_cat B C) X (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P X D h)) (@zero_arrow_family_incoming_transf B C t T X D
  h) (@one_cat_row_kernel_reconstruction_path B C S C1 t T P X D h)) (@eq_trans _ _ _ _ e (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C Y (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (λ v : τ (@Transf B C Y
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) X Y
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) v a)) (@zero_arrow_family_incoming_transf B C
  t T Y E k) (@comp_fapp0 (Functor_cat B C) Y (@kernel_adjunction_family_func B C S t T P E)
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P E) (@kernel_adjunction_family_boundary_transf B C S t T P Y E k)) (@eq_sym _ _ _
  (@one_cat_row_kernel_reconstruction_path B C S C1 t T P Y E k))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) X
  Y (@kernel_adjunction_family_func B C S t T P E) (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P E)
  (@kernel_adjunction_family_boundary_transf B C S t T P Y E k) a))))))));

// Use the existing whole square realization between the original boundary diagrams.
symbol one_cat_homology_family_boundary_map [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (X Y : τ (Functor B
  C)) (D E : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D)) (k : τ
  (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C D E m walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T X D h)) (@comp_fapp0
  (Functor_cat B C) X Y (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T Y E k) a)))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P X D
  h) (@kernel_adjunction_family_boundary_diagram_func B C S t T P Y E k))
≔ @one_cat_square_family_transf B C C1 X Y (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P E) (@kernel_adjunction_family_boundary_transf B C S t T P X D h)
  (@kernel_adjunction_family_boundary_transf B C S t T P Y E k) a (@kernel_adjunction_family_map_transf B C
  S C1 t T T0 P Q D E m) (@one_cat_homology_family_boundary_map_path B C S C1 t T T0 P Q X Y D E h k a m e);

// The original Q functor acts on that whole boundary map, retaining both original H objects.
symbol one_cat_homology_family_map_transf [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (X Y : τ (Functor B
  C)) (D E : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D)) (k : τ
  (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C D E m walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T X D h)) (@comp_fapp0
  (Functor_cat B C) X Y (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T Y E k) a)))
 : τ (@Transf B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) (@homology_adjunction_family_func B C
  S t T T0 P Q Y E k))
≔ @cokernel_adjunction_family_map_transf B C S C1 t T T0 P Q
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P X D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P Y E k) (@one_cat_homology_family_boundary_map
  B C S C1 t T T0 P Q X Y D E h k a m e);

// Whole quotient naturality reconstructs the original induced cycle map.
symbol one_cat_homology_family_map_projection_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (X Y : τ
  (Functor B C)) (D E : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  X) D)) (k : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C D E m walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T X D h)) (@comp_fapp0
  (Functor_cat B C) X Y (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T Y E k) a)))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T
  T0 P Q Y E k)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) (@homology_adjunction_family_func B C S t T T0 P Q Y E
  k) (@one_cat_homology_family_map_transf B C S C1 t T T0 P Q X Y D E h k a m e)
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) (@homology_adjunction_family_projection_transf B C S t
  T T0 P Q Y E k) (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)))
≔ (@eq_trans _ _ _ _ (@one_cat_cokernel_family_map_projection_path B C S C1 t T T0 P Q
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P X D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P Y E k) (@one_cat_homology_family_boundary_map
  B C S C1 t T T0 P Q X Y D E h k a m e)) (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P E)) (@Transf B C (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k)) (λ v : τ (@Transf B C (@kernel_adjunction_family_func
  B C S t T P D) (@kernel_adjunction_family_func B C S t T P E)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) (@homology_adjunction_family_projection_transf B C S t
  T T0 P Q Y E k) v)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P X D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P Y E k) (@one_cat_homology_family_boundary_map
  B C S C1 t T T0 P Q X Y D E h k a m e) walking_arrow_tgt) (@kernel_adjunction_family_map_transf B C S C1 t
  T T0 P Q D E m) (@one_cat_square_family_tgt_path B C C1 X Y (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P E) (@kernel_adjunction_family_boundary_transf B C S t T P X D h)
  (@kernel_adjunction_family_boundary_transf B C S t T P Y E k) a (@kernel_adjunction_family_map_transf B C
  S C1 t T T0 P Q D E m) (@one_cat_homology_family_boundary_map_path B C S C1 t T T0 P Q X Y D E h k a m
  e))));
