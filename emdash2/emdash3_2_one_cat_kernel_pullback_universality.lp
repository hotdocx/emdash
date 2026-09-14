/* Construct the inverse of the actual native kernel pullback comparison.
   Genuine ordinary profiles supply automatic coherence, never the inverse. */
require open emdash.emdash3_2_one_cat_kernel_pullback_lifts;
require open emdash.emdash3_2_discrete_functor_paths;
require open emdash.emdash3_2_one_cat_slice_paths;
require open emdash.emdash3_2_slice_sigma_arrow_paths;
require open emdash.emdash3_2_one_cat_functor_postcomposition_paths;

// Native functor for the already constructed inverse object program.
symbol one_cat_kernel_pullback_inverse_func [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  : τ (Functor (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C)
    X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)))
≔ @groupoidal_object_map_func (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat
  (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
    (@is_discrete_cat_core_equiv (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C
      D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) ((@one_cat_slice_category
      (Functor_cat B C) (@one_cat_functor_category B C C1) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src)) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D))) (λ h : τ (Obj (@pullback_cone_cat
      (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
      (@kernel_family_inclusion_slice B C S t T P D))), (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h));

// Original native lift recovered by the existing core reflection law.
symbol one_cat_kernel_pullback_inverse_point [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)))
    (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X
    D p a) h) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h))
≔ @groupoidal_object_map_point (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat
  (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
    (@is_discrete_cat_core_equiv (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C
      D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) ((@one_cat_slice_category
      (Functor_cat B C) (@one_cat_functor_category B C C1) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src)) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D))) (λ h : τ (Obj (@pullback_cone_cat
      (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
      (@kernel_family_inclusion_slice B C S t T P D))), (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h)) h;

// The actual inverse functor recovers the original first leg.
symbol one_cat_kernel_pullback_inverse_first_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat B C)
    (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
    (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying (Functor_cat B C) X a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S
    t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
    (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a) h))) (@slice_object_arrow (Functor_cat B C) X a))
≔ (@eq_trans (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat B C)
  (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
  (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying (Functor_cat B C) X a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
  (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a) h))) (@comp_fapp0 (Functor_cat B C)
  (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
  (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying (Functor_cat B C) X a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h)))
  (@slice_object_arrow (Functor_cat B C) X a) (@eq_ap (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p))) (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat
  B C) X a) X) (λ v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t
  T P X D p))), (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
  (@kernel_precomposition_family_func B C S t T P X D p) X (@kernel_precomposition_first_transf B C S t T P X D p)
  (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) v))) (@fapp0
  (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
  (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D
  p a) h) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h) (@one_cat_kernel_pullback_inverse_point B C S C1 t T T0
  P X D p a h)) (@one_cat_kernel_pullback_cone_lift_first_path B C S C1 t T T0 P X D p a h));

// Its second leg likewise recovers the complete original native cone arrow.
symbol one_cat_kernel_pullback_inverse_second_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t
    T P D)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
    (@kernel_precomposition_family_func B C S t T P X D p) (@kernel_adjunction_family_func B C S t T P D)
    (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p) (@slice_arrow_underlying (Functor_cat B C)
    X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S
    t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
    (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a) h))) (@slice_arrow_underlying (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S
    t T P D) h))
≔ (@eq_trans (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S
  t T P D)) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
  (@kernel_precomposition_family_func B C S t T P X D p) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p) (@slice_arrow_underlying (Functor_cat B C) X
  a (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
  (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a) h))) (@comp_fapp0 (Functor_cat B C)
  (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D
  p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
  (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h))) (@slice_arrow_underlying (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t
  T P D) h) (@eq_ap (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P
  X D p))) (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t
  T P D)) (λ v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X
  D p))), (@comp_fapp0 (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
  (@kernel_precomposition_family_func B C S t T P X D p) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p) (@slice_arrow_underlying (Functor_cat B C) X
  a (@kernel_precomposition_inclusion_slice B C S t T P X D p) v))) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
  (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a) h) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p
  a h) (@one_cat_kernel_pullback_inverse_point B C S C1 t T T0 P X D p a h)) (@one_cat_kernel_pullback_cone_lift_second_path B C S
  C1 t T T0 P X D p a h));

// Underlying arrow of the whole forward comparison.
symbol one_cat_kernel_pullback_forward_underlying [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p))))
  : τ (@= (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S t
    T P D)) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) (@fapp0 (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B
    C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B
    C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v)) (@comp_fapp0 (Functor_cat B
    C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)
    (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D
    p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)))
≔ @eq_trans (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C S
  t T P D)) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) (@fapp0 (Hom_cat (@Slice_cat
  (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B
  C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C
  S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v)) (@comp_fapp0 (Functor_cat B C)
  (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D
  p) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
  (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
  (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@fapp1_fapp0 (@Slice_cat (Functor_cat B C) X) (@Slice_cat
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@slice_sigma_func
  (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p) v))) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
  (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) (@kernel_adjunction_family_func B C S
  t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p) (@slice_arrow_underlying
  (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) v))
    (@one_cat_functor_postcomp_path (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C
      D walking_arrow_src)) (Functor_cat B C) (@one_cat_functor_category B C C1) (@slice_domain_func (Functor_cat B C)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
      (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
        (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
        (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@kernel_family_inclusion_slice B C S t T P D)
        (@one_cat_kernel_pullback_slice_arrow B C S C1 t T T0 P X D p) (@fapp1_fapp0 (@Slice_cat (Functor_cat B C) X)
        (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
        (@slice_sigma_func (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p) a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) v))
    (@eq_ap (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B
      C S t T P X D p)) (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a)
      (@kernel_adjunction_family_func B C S t T P D)) (λ u : τ (Hom (Functor_cat B C) (@slice_object_domain
      (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)), (@comp_fapp0 (Functor_cat B C)
      (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)
      (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X
      D p) u))
      (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
        (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
        (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@fapp1_fapp0 (@Slice_cat (Functor_cat B C) X)
        (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
        (@slice_sigma_func (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p) a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)) (@slice_arrow_underlying (Functor_cat B C) X a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) v) (@slice_sigma_underlying_path (Functor_cat B
        C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) v));

// The inverse object program reconstructs the entire native cone.
symbol one_cat_kernel_pullback_right_object_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))) (@fapp0 (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B
    C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B
    C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) (@one_cat_kernel_pullback_cone_lift B C S C1
    t T T0 P X D p a h)) h)
≔ @one_cat_slice_arrow_path (Functor_cat B C) (@one_cat_functor_category B C C1) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) (@fapp0 (Hom_cat
  (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat
  (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
  (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p
  a) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h)) h
    (@eq_trans (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_adjunction_family_func B C
      S t T P D)) (@slice_arrow_underlying (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t T P D) (@fapp0 (Hom_cat (@Slice_cat
      (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat
      B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
      (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X
      D p a) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h))) (@comp_fapp0 (Functor_cat B C)
      (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p)
      (@kernel_adjunction_family_func B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X
      D p) (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
      (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h))) (@slice_arrow_underlying (Functor_cat B C)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@slice_sigma_obj (Functor_cat B C) X
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C
      S t T P D) h) (@one_cat_kernel_pullback_forward_underlying B C S C1 t T T0 P X D p a (@one_cat_kernel_pullback_cone_lift B C
      S C1 t T T0 P X D p a h)) (@one_cat_kernel_pullback_cone_lift_second_path B C S C1 t T T0 P X D p a h));

// The original kernel inclusion determines the complete native slice lift.
symbol one_cat_kernel_pullback_left_object_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p))))
  : τ (@= (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)))
    (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S
    t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v)) v)
≔ @one_cat_slice_arrow_path (Functor_cat B C) (@one_cat_functor_category B C C1) X a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a (@fapp0
  (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
  (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
  (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p
  a) v)) v
    (@one_cat_kernel_family_inclusion_reflect_path B C S C1 t T T0 P (@slice_object_domain (Functor_cat B C) X a)
      (@precomposed_diagram_family_func B C X D p)
      (@slice_arrow_underlying (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p)
        (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B
        C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v))) (@slice_arrow_underlying
        (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)
      (@eq_trans (Hom (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat B C)
        (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
        (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying (Functor_cat B C) X a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a
        (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
        (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
        (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P
        X D p a) v)))) (@slice_object_arrow (Functor_cat B C) X a) (@comp_fapp0 (Functor_cat B C)
        (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
        (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying (Functor_cat B C) X a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)) (@one_cat_kernel_pullback_cone_lift_first_path B C S C1 t T
        T0 P X D p a (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t
        T P X D p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))
        (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v)) (@eq_sym (Hom (Functor_cat B C)
        (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat B C) (@slice_object_domain
        (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
        (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying (Functor_cat B C) X a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)) (@slice_object_arrow (Functor_cat B C) X a)
        (@hom_to_path (Hom_cat (Functor_cat B C) (@slice_object_domain (Functor_cat B C) X a) X)
        ((@one_cat_functor_category B C C1) (@slice_object_domain (Functor_cat B C) X a) X) (@comp_fapp0 (Functor_cat
        B C) (@slice_object_domain (Functor_cat B C) X a) (@kernel_precomposition_family_func B C S t T P X D p) X
        (@kernel_precomposition_first_transf B C S t T P X D p) (@slice_arrow_underlying (Functor_cat B C) X a
        (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)) (@slice_object_arrow (Functor_cat B C) X a)
        (@slice_arrow_cell (Functor_cat B C) X a (@kernel_precomposition_inclusion_slice B C S t T P X D p) v)))));

// The native inverse functor satisfies the right object law at the original h.
symbol one_cat_kernel_pullback_right_point_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (h : τ (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
  : τ (@= (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))) (@fapp0 (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B
    C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B
    C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) (@fapp0 (@pullback_cone_cat
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X
    D p a) h)) h)
≔ (@eq_trans (Obj (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))) (@fapp0 (Hom_cat (@Slice_cat
  (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B
  C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C
  S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) (@fapp0 (@pullback_cone_cat
  (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
  (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D
  p a) h)) (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
  p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
  (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p
  a) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h)) h (@eq_ap (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p))) (Obj (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D))) (λ v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P
  X D p))), (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
  p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
  (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p
  a) v)) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C)
  X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P
  X D p a) h) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a h) (@one_cat_kernel_pullback_inverse_point B C S C1 t T
  T0 P X D p a h)) (@one_cat_kernel_pullback_right_object_path B C S C1 t T T0 P X D p a h));

// The native inverse functor satisfies the left object law at the original v.
symbol one_cat_kernel_pullback_left_point_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X))) (v : τ (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p))))
  : τ (@= (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)))
    (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X
    D p a) (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
    p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D
    p a) v)) v)
≔ (@eq_trans (Obj (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
  p))) (@fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C)
  X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P
  X D p a) (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
  p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
  (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p
  a) v)) (@one_cat_kernel_pullback_cone_lift B C S C1 t T T0 P X D p a (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v)) v
  (@one_cat_kernel_pullback_inverse_point B C S C1 t T T0 P X D p a (@fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) v))
  (@one_cat_kernel_pullback_left_object_path B C S C1 t T T0 P X D p a v));

// Automatic coherence into the actual zero-target yields the whole left law.
symbol one_cat_kernel_pullback_left_functor_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  : τ (@= (Functor (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
    p)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)))
    (@comp_cat_fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
    p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X
    D p a) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a)) (@id_func (Hom_cat (@Slice_cat
    (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))))
≔ @discrete_functor_path (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S
  t T P X D p)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
  ((@one_cat_slice_category (Functor_cat B C) (@one_cat_functor_category B C C1) X) a
  (@kernel_precomposition_inclusion_slice B C S t T P X D p))
    (@comp_cat_fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D
      p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
      a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B C) X) a
      (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P
      X D p a) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a)) (@id_func (Hom_cat (@Slice_cat
      (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)))
    (@one_cat_kernel_pullback_left_point_path B C S C1 t T T0 P X D p a);

// The right law likewise retains the entire native cone Hom action.
symbol one_cat_kernel_pullback_right_functor_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  : τ (@= (Functor (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (@pullback_cone_cat (Functor_cat B C)
    X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C
    S t T P D))) (@comp_cat_fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat
    C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat
    B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S
    t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a) (@one_cat_kernel_pullback_inverse_func
    B C S C1 t T T0 P X D p a)) (@id_func (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))))
≔ @discrete_functor_path (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D)) ((@one_cat_slice_category (Functor_cat B C) (@one_cat_functor_category B C C1)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@slice_sigma_obj (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a) (@kernel_family_inclusion_slice B C S t
  T P D))
    (@comp_cat_fapp0 (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (Hom_cat (@Slice_cat (Functor_cat B
      C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C
      S t T P D)) (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a)
      (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a)) (@id_func (@pullback_cone_cat (Functor_cat B C)
      X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B
      C S t T P D)))
    (@one_cat_kernel_pullback_right_point_path B C S C1 t T T0 P X D p a);

// Fixed-forward native equivalence constructed with the same actual inverse.
symbol one_cat_kernel_pullback_comparison_equiv [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  : τ (@OmegaEquivAlong Cat_cat (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S
    t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D))
    (@one_cat_kernel_pullback_comparison_func B C S C1 t T T0 P X D p a))
≔ @omega_equiv_along_intro Cat_cat (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B
  C S t T P X D p)) (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t T P D)) (@one_cat_kernel_pullback_comparison_func
  B C S C1 t T T0 P X D p a) (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a)
  (@one_cat_kernel_pullback_inverse_func B C S C1 t T T0 P X D p a)
    (@one_cat_kernel_pullback_left_functor_path B C S C1 t T T0 P X D p a)
    (@one_cat_kernel_pullback_right_functor_path B C S C1 t T T0 P X D p a);
