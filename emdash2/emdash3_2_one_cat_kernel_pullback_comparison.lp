/* Native slice-Hom comparison for the already commuting kernel square.
   This constructs the forward functor before proving its invertibility.
   It does not assume a PullbackStructure or introduce a cone record. */
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_pullbacks;

// The original first inclusion is an object of the native slice over X.
symbol kernel_precomposition_inclusion_slice [B C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (p : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) : τ (Obj (@Slice_cat (Functor_cat B C) X))
≔ (@Struct_sigma (Obj (Functor_cat B C)) (λ z : τ (Obj (Functor_cat B C)), Hom (Functor_cat B C) z X)
  (@kernel_precomposition_family_func B C S t T P X D p) (@kernel_precomposition_first_transf B C S t T P X D p));

// The original κ_D is an object of the native slice over E₀D.
symbol kernel_family_inclusion_slice [B C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) : τ (Obj (@Slice_cat (Functor_cat B C) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_src)))
≔ (@Struct_sigma (Obj (Functor_cat B C)) (λ z : τ (Obj (Functor_cat B C)), Hom (Functor_cat B C) z
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D));

// The proved square is one native slice arrow Σ_p(κ_dp)→κ_d.
symbol one_cat_kernel_pullback_slice_arrow [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  : τ (Hom (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
    (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
    (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@kernel_family_inclusion_slice B C S t T P D))
≔ @slice_arrow_intro (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
  (@kernel_precomposition_inclusion_slice B C S t T P X D p)) (@kernel_family_inclusion_slice B C S t T P D)
  (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p) (@path_to_hom (Hom_cat (Functor_cat B C)
  (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p)
  (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t
  T T0 P X D p)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p (@kernel_precomposition_first_transf B C S t T
  P X D p)) (@one_cat_kernel_precomposition_square_path B C S C1 t T T0 P X D p));

// The entire comparison is slice postcomposition after Σ_p's native Hom action.
symbol one_cat_kernel_pullback_comparison_func [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (a : τ (Obj (@Slice_cat
    (Functor_cat B C) X)))
  : τ (Functor (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
    (@pullback_cone_cat (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a
    (@kernel_family_inclusion_slice B C S t T P D)))
≔ @comp_cat_fapp0 (Hom_cat (@Slice_cat (Functor_cat B C) X) a (@kernel_precomposition_inclusion_slice B C S t T P X D p))
  (Hom_cat (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a)
  (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
  (@kernel_precomposition_inclusion_slice B C S t T P X D p))) (@pullback_cone_cat (Functor_cat B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p a (@kernel_family_inclusion_slice B C S t
  T P D))
    (@hom_postcomp_func (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src)) (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src)) (@id_func (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src))) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p a) (@slice_sigma_obj (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) p (@kernel_precomposition_inclusion_slice B C S t T P X D p))
      (@kernel_family_inclusion_slice B C S t T P D) (@one_cat_kernel_pullback_slice_arrow B C S C1 t T T0 P X D
      p))
    (@fapp1_func (@Slice_cat (Functor_cat B C) X) (@Slice_cat (Functor_cat B C) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src)) (@slice_sigma_func (Functor_cat B C) X (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) p) a (@kernel_precomposition_inclusion_slice B C S t T P X D p));
