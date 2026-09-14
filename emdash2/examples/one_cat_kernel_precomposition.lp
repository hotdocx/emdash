/* Kernel of the precomposed family: actual data and native comparison.
   These checks do not assert the pending cartesian universal property. */
require open emdash.emdash3_2_one_cat_kernel_precomposition;

assert [B C : Cat] (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) ⊢
    (@diagram_family_at_func B WalkingArrow_cat C (@precomposed_diagram_family_func B C X D p) walking_arrow_src) ≡
    X;
assert [B C : Cat] (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) ⊢
    (@diagram_family_at_func B WalkingArrow_cat C (@precomposed_diagram_family_func B C X D p) walking_arrow_tgt) ≡
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt);
assert [B C : Cat] (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) ⊢ (@diagram_family_transf
    B WalkingArrow_cat C (@precomposed_diagram_family_func B C X D p) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) ≡ (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
    WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) p);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (b : τ (Obj B))
  ⊢ @fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p) b
    ≡ @fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 B (Functor_cat
      WalkingArrow_cat C) (@precomposed_diagram_family_func B C X D p) b);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@one_cat_kernel_precomposition_projection_zero_path B C S C1 t T T0 P X D p) : τ (@= (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt))
      (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func
        B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) X
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p (@kernel_precomposition_first_transf B C S
        t T P X D p))) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_precomposition_family_func B C S t T P X D
        p) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)));

// Complete input recovery retains p and the first original inclusion.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P) (@kernel_precomposition_family_func B C S t T P X D p) D)
    (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)) ≡ @one_cat_kernel_family_input B C C1 t T T0
    (@kernel_precomposition_family_func B C S t T P X D p) D (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p (@kernel_precomposition_first_transf B C S t T P X D p))
    (@one_cat_kernel_precomposition_projection_zero_path B C S C1 t T T0 P X D p);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@one_cat_kernel_precomposition_reconstruction_path B C S C1 t T T0 P X D p) : τ (@= (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_precomposition_family_func B C S t T P X D p))
    D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P) (@kernel_precomposition_family_func B C S t T P X D p) D)
    (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p (@kernel_precomposition_first_transf B C S t T P X D p)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ @one_cat_kernel_family_lift_unique B C S C1 t T T0 P (@kernel_precomposition_family_func B C S t T P X D p) D
    (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_src) p (@kernel_precomposition_first_transf B C S t T P X D p))
    (@one_cat_kernel_precomposition_projection_zero_path B C S C1 t T T0 P X D p)
      (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p) (@one_cat_kernel_precomposition_reconstruction_path B C S
        C1 t T T0 P X D p) : τ (@= (@Transf B C (@kernel_precomposition_family_func B C S t T P X D p)
        (@kernel_adjunction_family_func B C S t T P D)) (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)
        (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p));

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (p0 : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@one_cat_kernel_precomposition_reconstruction_path B C S C1 t T T0 P X D p) : τ (@= (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_precomposition_family_func B C S t T P X D p))
    D (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P) (@kernel_precomposition_family_func B C S t T P X D p) D)
    (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
    (@kernel_precomposition_family_func B C S t T P X D p) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) p0 (@kernel_precomposition_first_transf B C S t T P X D p)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (b b' : τ (Obj B))
  ⊢ @tapp1_func B C (@kernel_precomposition_family_func B C S t T P X D p) (@kernel_adjunction_family_func B C S t T
    P D) b b' (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)
    : τ (Functor (Hom_cat B b b') (Hom_cat C (@fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p) b)
      (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) b')));
