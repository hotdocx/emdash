/* Native cone objects feed the original whole kernel mate. */
require open emdash.emdash3_2_one_cat_kernel_pullback_comparison;
require open emdash.emdash3_2_eq1_evidence_property;

// Whole zero postcomposition through the existing terminal-family uniqueness.
symbol one_cat_zero_family_precompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X A Y : τ (Functor B C)) (u : τ (@Transf B C X A))
  : τ (@= (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X A Y (@zero_arrow_family_zero_transf B C t T T0 A Y) u)
    (@zero_arrow_family_zero_transf B C t T T0 X Y))
≔ @eq_ap (@Transf B C X (@Const_func B C t)) (@Transf B C X Y)
    (λ j : τ (@Transf B C X (@Const_func B C t)), (@comp_fapp0 (Functor_cat B C) X (@Const_func B C t) Y
      (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src walking_arrow_tgt walking_arrow_generator) j))
    (@comp_fapp0 (Functor_cat B C) X A (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) walking_arrow_src
      walking_arrow_tgt walking_arrow_generator) u) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
      (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
      walking_arrow_generator)
    (@one_cat_terminal_family_arrow_path B C C1 t T X (@comp_fapp0 (Functor_cat B C) X A (@Const_func B C t)
      (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) walking_arrow_src walking_arrow_tgt walking_arrow_generator) u));

// The native slice-Hom cell is an ordinary whole equation in this genuine 0-Hom.
symbol one_cat_kernel_pullback_cone_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
    (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@slice_arrow_underlying (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S
    t T P D) h)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p (@slice_object_arrow (Functor_cat B C) X a)))
≔ @hom_to_path (Hom_cat (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src))
    ((@one_cat_functor_category B C C1) (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C)
      X a) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@slice_arrow_underlying
      (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj
      (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
      (@kernel_family_inclusion_slice B C S t T P D) h)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
      (Functor_cat B C) X a) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
      (@slice_object_arrow (Functor_cat B C) X a)) (@slice_arrow_cell (Functor_cat B C) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h);

// Derive the composite annihilation from the native cone, without a new caller field.
symbol one_cat_kernel_pullback_cone_zero [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) p) (@slice_object_arrow (Functor_cat B C) X a)) (@zero_arrow_family_zero_transf B C t T
    T0 (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt)))
≔ @eq_trans (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) p) (@slice_object_arrow (Functor_cat B C) X a)) (@comp_fapp0 (Functor_cat B C)
  (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P
  D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@slice_arrow_underlying
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat
  B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice
  B C S t T P D) h)) (@zero_arrow_family_zero_transf B C t T T0 (@slice_object_domain (Functor_cat B C) X a)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
    (@eq_ap (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src)) (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt))
      (λ f : τ (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C
        D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat
        C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
        walking_arrow_generator) f)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p (@slice_object_arrow (Functor_cat B C) X
        a)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
        (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@slice_arrow_underlying
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj
        (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
        (@kernel_family_inclusion_slice B C S t T P D) h))
      (@eq_sym (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C
        D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
        (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@slice_arrow_underlying
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj
        (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
        (@kernel_family_inclusion_slice B C S t T P D) h)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
        (Functor_cat B C) X a) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
        (@slice_object_arrow (Functor_cat B C) X a)) (@one_cat_kernel_pullback_cone_path B C S C1 t T T0 P X D p a h)))
    (@eq_trans (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C
      D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
      (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
      D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
      walking_arrow_generator) (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@slice_arrow_underlying
      (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj
      (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
      (@kernel_family_inclusion_slice B C S t T P D) h)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
      (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt) (@zero_arrow_family_zero_transf B C t T T0
      (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt)) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h)) (@zero_arrow_family_zero_transf
      B C t T T0 (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt))
      (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat
        C D walking_arrow_tgt)) (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_tgt))
        (λ f : τ (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B
          WalkingArrow_cat C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat
          B C) X a) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_tgt) f (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat
          C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h))) (@comp_fapp0 (Functor_cat B
          C) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
          (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
          (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@zero_arrow_family_zero_transf B C t T T0
          (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_tgt))
        (@one_cat_kernel_family_annihilation_path B C S C1 t T T0 P D))
      (@one_cat_zero_family_precompose_path B C C1 t T T0 (@slice_object_domain (Functor_cat B C) X a)
        (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_tgt) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h)));

// Produce a native lift in the original slice over X.
symbol one_cat_kernel_pullback_cone_lift [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (Hom (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
≔ @slice_arrow_intro (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
  (@one_cat_kernel_family_lift B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
  (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a) (@one_cat_kernel_pullback_cone_zero B
  C S C1 t T T0 P X D p a h))
    (@path_to_hom (Hom_cat (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat
      B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
      (@kernel_precomposition_first_transf B C S t T P X D p) (@one_cat_kernel_family_lift B C S C1 t T T0 P
      (@slice_object_domain (Functor_cat B C) X a) (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow
      (Functor_cat B C) X a) (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h))) (@slice_object_arrow (Functor_cat
      B C) X a) (@one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P (@slice_object_domain
      (Functor_cat B C) X a) (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a)
      (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h)));

// Its first leg is exactly the original whole source arrow.
symbol one_cat_kernel_pullback_cone_lift_first_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (@Transf B C (@slice_object_domain (Functor_cat B C) X a) X)
      (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func
        B C S t T P X D p) X (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying
        (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@one_cat_kernel_pullback_cone_lift B C S
        C1 t T T0 P X D p a h))) (@slice_object_arrow (Functor_cat B C) X a))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
  (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a) (@one_cat_kernel_pullback_cone_zero B
  C S C1 t T T0 P X D p a h));

// The second leg is recovered by whole monicity of the original κ_D.
symbol one_cat_kernel_pullback_cone_lift_second_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t T P D))
    (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B
    C S t T P X D p) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C
    S C1 t T T0 P X D p) (@one_cat_kernel_family_lift B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
    (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a) (@one_cat_kernel_pullback_cone_zero
    B C S C1 t T T0 P X D p a h))) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h))
≔ @one_cat_kernel_family_inclusion_reflect_path B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a) D
  (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C
  S t T P X D p) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1
  t T T0 P X D p) (@one_cat_kernel_family_lift B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
  (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a) (@one_cat_kernel_pullback_cone_zero B
  C S C1 t T T0 P X D p a h))) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h)
    (@eq_trans (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C
      D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
      (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@comp_fapp0 (Functor_cat B C)
      (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)
      (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X
      D p) (@one_cat_kernel_family_lift B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
      (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a)
      (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h)))) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
      (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S
      t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
      (@kernel_precomposition_first_transf B C S t T P X D p)) (@one_cat_kernel_family_lift B C S C1 t T T0 P
      (@slice_object_domain (Functor_cat B C) X a) (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow
      (Functor_cat B C) X a) (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h))) (@comp_fapp0 (Functor_cat B C)
      (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t T P D)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
      C S t T P D) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h))
      (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@slice_object_domain (Functor_cat B C) X a)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
        (λ f : τ (@Transf B C (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
          WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat
          B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat
          C D walking_arrow_src) f (@one_cat_kernel_family_lift B C S C1 t T T0 P (@slice_object_domain (Functor_cat B
          C) X a) (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a)
          (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h))))
        (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p)
          (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D)
          (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)) (@comp_fapp0 (Functor_cat B C)
          (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_src) p (@kernel_precomposition_first_transf B C S t T P X D p))
        (@one_cat_kernel_precomposition_square_path B C S C1 t T T0 P X D p))
      (@eq_trans (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat
        C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
        (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) X
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p (@kernel_precomposition_first_transf B C
        S t T P X D p)) (@one_cat_kernel_family_lift B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
        (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a)
        (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h))) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
        (Functor_cat B C) X a) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
        (@slice_object_arrow (Functor_cat B C) X a)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat
        B C) X a) (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@slice_arrow_underlying
        (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj
        (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
        (@kernel_family_inclusion_slice B C S t T P D) h))
        (@eq_ap (@Transf B C (@slice_object_domain (Functor_cat B C) X a) X) (@Transf B C (@slice_object_domain
          (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
          (λ f : τ (@Transf B C (@slice_object_domain (Functor_cat B C) X a) X), (@comp_fapp0 (Functor_cat B C)
            (@slice_object_domain (Functor_cat B C) X a) X (@diagram_family_at_func B WalkingArrow_cat C D
            walking_arrow_src) p f)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
            (@kernel_precomposition_family_func B C S t T P X D p) X (@kernel_precomposition_first_transf B C S t T P
            X D p) (@one_cat_kernel_family_lift B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
            (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a)
            (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h))) (@slice_object_arrow (Functor_cat B C) X a)
            (@one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P (@slice_object_domain (Functor_cat B
            C) X a) (@precomposed_diagram_family_func B C X D p) (@slice_object_arrow (Functor_cat B C) X a)
            (@one_cat_kernel_pullback_cone_zero B C S C1 t T T0 P X D p a h)))
        (@eq_sym (@Transf B C (@slice_object_domain (Functor_cat B C) X a) (@diagram_family_at_func B WalkingArrow_cat
          C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
          (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
          walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@slice_arrow_underlying
          (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj
          (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
          (@kernel_family_inclusion_slice B C S t T P D) h)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
          (Functor_cat B C) X a) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
          (@slice_object_arrow (Functor_cat B C) X a)) (@one_cat_kernel_pullback_cone_path B C S C1 t T T0 P X D p a h))));
