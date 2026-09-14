/* Original kernel inclusion, native Γ and the actual precomposition square. */
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (v : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
  ⊢ (@fapp0 (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))
    (@one_cat_kernel_family_projection_func B C S C1 t T P X D) v) ≡ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) X D) v) walking_arrow_src);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (v : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
  ⊢ @one_cat_kernel_family_projection_functor_path B C S C1 t T P X D v
    : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@fapp0 (Hom_cat
      (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
      (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
      (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
      (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat
      B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat
      B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))
      (@one_cat_kernel_family_projection_func B C S C1 t T P X D) v) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0
      B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P D) v));

// Its next Hom action is retained at the native source and target.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (u v : τ (Obj (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat
    B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D))))
  ⊢ @fapp1_func (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))
    (@one_cat_kernel_family_projection_func B C S C1 t T P X D) u v
    : τ (Functor (Hom_cat (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      D)) u v)
      (Hom_cat (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
        (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D)) (@fapp0
        (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
        (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
        (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
        (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C)
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))
        (@one_cat_kernel_family_projection_func B C S C1 t T P X D) u) (@fapp0 (Hom_cat (Functor_cat B C) X (@fapp0
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
        WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat
        B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
        walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
        (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X)) (@fapp0
        (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
        WalkingArrow_cat C walking_arrow_src) D)) (@one_cat_kernel_family_projection_func B C S C1 t T P X D) v)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D
    : τ (Functor B (Functor_cat WalkingArrow_cat C))) (u v : τ (Obj (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat
    B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D)))) (alpha : τ (Hom (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) D)) u v))
  ⊢ @fapp1_fapp0 (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
    (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
    C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))
    (@one_cat_kernel_family_projection_func B C S C1 t T P X D) u v alpha
    : τ (Hom (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
      (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat
      B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat
      B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D)) (@fapp0 (Hom_cat (Functor_cat
      B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
      (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B C) (@fapp0
      (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
      WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X)) (@fapp0
      (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
      WalkingArrow_cat C walking_arrow_src) D)) (@one_cat_kernel_family_projection_func B C S C1 t T P X D) u) (@fapp0
      (Hom_cat (Functor_cat B C) X (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
      (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat
      (Functor_cat B C) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
      (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat B C) (Functor_cat
      B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) X)) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat
      B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) D))
      (@one_cat_kernel_family_projection_func B C S C1 t T P X D) v));

// Original κ after the lift is the original whole k.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  ⊢ @one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P X D k z
    : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
      (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
      C S t T P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) k);

// Actual use of whole monicity at two independently supplied lifts of the same source.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  (z0 : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  ⊢ @one_cat_kernel_family_inclusion_reflect_path B C S C1 t T T0 P X D
      (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z0)
      (@eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
        (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D
        k z)) k
        (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
          (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
          (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X
          D k z0))
        (@one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P X D k z)
        (@eq_sym (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0
          (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T
          P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
          (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X
          D k z0)) k
          (@one_cat_kernel_family_lift_ambient_reconstruction B C S C1 t T T0 P X D k z0)))
    : τ (@= (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
      D)) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k
      z0));

// The actual square uses both original selected inclusions and the constructed r.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
    (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) ⊢
    (@one_cat_kernel_precomposition_square_path B C S C1 t T T0 P X D p) : τ (@= (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
    S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)) (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p (@kernel_precomposition_first_transf B C S t T P X D p)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
    (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@kernel_precomposition_first_transf B C S t T P X D p) ≡ @kernel_adjunction_family_inclusion_transf B C S t T P
    (@precomposed_diagram_family_func B C X D p);
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
    (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (p0 : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@one_cat_kernel_precomposition_square_path B C S C1 t T T0 P X D p) : τ (@= (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C
    S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)) (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p0 (@kernel_precomposition_first_transf B C S t T P X D p)));

// Evaluation retains the actual parameter object and gives its ordinary square.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
    (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
    (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (b : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src)) (Hom C (@fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p)
    b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b))
      (λ h : τ (@Transf B C (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src)), @tapp0_fapp0 B C (@kernel_precomposition_family_func B C S t T P X D
        p) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b h) (@comp_fapp0 (Functor_cat B C)
        (@kernel_precomposition_family_func B C S t T P X D p) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S
        C1 t T T0 P X D p)) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) X
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p (@kernel_precomposition_first_transf B C
        S t T P X D p)) (@one_cat_kernel_precomposition_square_path B C S C1 t T T0 P X D p)
    : τ (@= (Hom C (@fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p) b) (@fapp0 B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b))
      (@tapp0_fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) b (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B
        C S t T P X D p) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf
        B C S t T P D) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)))
      (@tapp0_fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) b (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B
        C S t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
        (@kernel_precomposition_first_transf B C S t T P X D p))));
