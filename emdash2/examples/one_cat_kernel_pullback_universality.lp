/* Original kernel square: native universal comparison and both inverse laws. */
require open emdash.emdash3_2_one_cat_kernel_pullback_universality;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ @slice_object_domain (Functor_cat B C) X (@kernel_precomposition_inclusion_slice B C S t T P X D p) ≡
    (@kernel_precomposition_family_func B C S t T P X D p);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ @slice_object_arrow (Functor_cat B C) X (@kernel_precomposition_inclusion_slice B C S t T P X D p) ≡
    (@kernel_precomposition_first_transf B C S t T P X D p);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ @slice_object_domain (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@kernel_family_inclusion_slice B C S t T P D) ≡ (@kernel_adjunction_family_func B C S t T P D);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ @slice_object_arrow (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@kernel_family_inclusion_slice B C S t T P D) ≡ (@kernel_adjunction_family_inclusion_transf B C S t T P D);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@kernel_family_inclusion_slice B C S t T P D)
    (@one_cat_kernel_pullback_slice_arrow B C S C1 t T T0 P X D p)) ≡ (@one_cat_kernel_precomposition_second_transf B
    C S C1 t T T0 P X D p);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) : τ (Functor (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a) : τ (Functor (@pullback_cone_cat (Functor_cat B
    C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S
    t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
    p)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@one_cat_kernel_pullback_inverse_point B C S C1 t T T0 P X D p a h) : τ (@= (Obj (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))) (@fapp0 (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) h) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@one_cat_kernel_pullback_cone_lift_first_path B C S C1 t T T0 P X D p a h) : τ (@= (Hom (Functor_cat B C)
    (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat
    B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X (@kernel_precomposition_first_transf B C S t T
    P X D p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
    (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h))) (@slice_object_arrow (Functor_cat B C) X a));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@one_cat_kernel_pullback_cone_lift_second_path B C S C1 t T T0 P X D p a h) : τ (@= (Hom (Functor_cat B C)
    (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0
    (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D
    p) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P
    X D p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
    (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h))) (@slice_arrow_underlying (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T
    P D) h));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@one_cat_kernel_pullback_inverse_first_path B C S C1 t T T0 P X D p a h) : τ (@= (Hom (Functor_cat B C)
    (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat
    B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X (@kernel_precomposition_first_transf B C S t T
    P X D p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
    (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) h))) (@slice_object_arrow (Functor_cat B C) X a));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@one_cat_kernel_pullback_inverse_second_path B C S C1 t T T0 P X D p a h) : τ (@= (Hom (Functor_cat B C)
    (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0
    (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D
    p) (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P
    X D p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
    (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) h))) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) h));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p))))
  ⊢ (@one_cat_kernel_pullback_forward_underlying B C S C1 t T T0 P X D p a v) : τ (@= (Hom (Functor_cat B C)
    (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t T P D))
    (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
    (@kernel_family_inclusion_slice B C S t T P D) (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P
    D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v)) (@comp_fapp0 (Functor_cat B C)
    (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D
    p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@one_cat_kernel_pullback_right_point_path B C S C1 t T T0 P X D p a h) : τ (@= (Obj (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D))) (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P
    D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) (@fapp0 (@pullback_cone_cat (Functor_cat
    B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C
    S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
    p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a) h)) h);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p))))
  ⊢ (@one_cat_kernel_pullback_left_point_path B C S C1 t T T0 P X D p a v) : τ (@= (Obj (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))) (@fapp0 (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P
    X D p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    p a (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X
    D p a) v)) v);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@one_cat_kernel_pullback_left_functor_path B C S C1 t T T0 P X D p a) : τ (@= (Functor (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))) (@comp_cat_fapp0 (Hom_cat
    (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a)) (@id_func (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@one_cat_kernel_pullback_right_functor_path B C S C1 t T T0 P X D p a) : τ (@= (Functor (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))) (@comp_cat_fapp0
    (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P
    D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) (@one_cat_kernel_pullback_inverse_func B
    C S C1 t T T0 P X D p a)) (@id_func (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@one_cat_kernel_pullback_comparison_equiv B C S C1 t T T0 P X D p a) : τ (@OmegaEquivAlong Cat_cat (Hom_cat
    (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p
    a));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@omega_equiv_along_left_inv Cat_cat (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P
    D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a)
    (@one_cat_kernel_pullback_comparison_equiv B C S C1 t T T0 P X D p a)) ≡ (@one_cat_kernel_pullback_inverse_func B
    C S C1 t T T0 P X D p a);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@omega_equiv_along_right_inv Cat_cat (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P
    D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a)
    (@one_cat_kernel_pullback_comparison_equiv B C S C1 t T T0 P X D p a)) ≡ (@one_cat_kernel_pullback_inverse_func B
    C S C1 t T T0 P X D p a);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h g : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@fapp1_func (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) h g) : τ (Functor (Hom_cat (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) h g) (Hom_cat (Hom_cat
    (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@fapp0
    (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) h) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) g)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h g : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)))) (alpha : τ (Hom
    (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) h g))
  ⊢ (@fapp1_fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) h g alpha) : τ (Hom (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice
    B C S t T P X D p)) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C
    D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X)
    a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T
    T0 P X D p a) h) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) g));

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  ⊢ (@comp_cat_fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X
    D p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
    a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0
    P X D p a) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a)) ≡ (@id_func (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)));

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h g : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  ⊢ (@eq_refl (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))) h) : τ (@= (Obj (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D))) h g);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (v w : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p))))
  ⊢ (@eq_refl (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
    p))) v) : τ (@= (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T
    P X D p))) v w);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (p2 : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p) : τ (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p2) (@kernel_adjunction_family_func B C S t T P D));
