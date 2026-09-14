/* Whole kernel lifting: original inputs, native cancellation and action. */
require open emdash.emdash3_2_one_cat_kernel_family_lift;

// Native inverse mating recovers the complete introduced input at D itself.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) ≡
    (@one_cat_kernel_family_input B C C1 t T T0 X D k z);

// Whole source recovery is the original k, without another premise.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ (@one_cat_kernel_family_lift_reconstruction
    B C S C1 t T T0 P X D k z) : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))
    walking_arrow_src) k);

// The uniqueness program consumes reconstruction of the same whole source.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (b : τ (@Transf B C X (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))) (p : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) X D) b) walking_arrow_src) k))
  ⊢ @one_cat_kernel_family_lift_unique B C S C1 t T T0 P X D k z b p
    : τ (@= (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
      D)) b (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z));

// Different annihilation witnesses give the same whole lift.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
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
  ⊢ @one_cat_kernel_family_lift_unique B C S C1 t T T0 P X D k z
      (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z0)
      (@one_cat_kernel_family_lift_reconstruction B C S C1 t T T0 P X D k z0)
    : τ (@= (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
      D)) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z0) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k
      z));

// An unrelated source transformation cannot replace k in reconstruction.
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (k0 : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@one_cat_kernel_family_lift_reconstruction B C S C1 t T T0 P X D k z) : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D (@fapp0 _ _
    (@one_cat_adjunction_family_untranspose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) X D) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z))
    walking_arrow_src) k0);

// The original K(D), including D's actual point, is retained.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (b : τ (Obj B))
  ⊢ @fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) b
    ≡ @fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 B (Functor_cat
      WalkingArrow_cat C) D b);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) b
    (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)
    : τ (Hom C (@fapp0 B C X b)
        (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 B (Functor_cat
          WalkingArrow_cat C) D b)));

// Whole off-diagonal action has the original endpoint families.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (b b' : τ (Obj B))
  ⊢ @tapp1_func B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) b
    b' (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)
    : τ (Functor (Hom_cat B b b') (Hom_cat C (@fapp0 B C X b) (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat
      WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) b')));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (b b' : τ (Obj B)) (a : τ (Hom B b b'))
  ⊢ @tapp1_fapp0 B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) b
    b' (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z) a
    : τ (Hom C (@fapp0 B C X b) (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T P) D) b'));

// The next Hom functor is retained, not just its point application.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (b b' : τ (Obj B)) (a a' : τ (Hom B b b'))
  ⊢ @fapp1_func (Hom_cat B b b') (Hom_cat C (@fapp0 B C X b) (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) b'))
      (@tapp1_func B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
        b b' (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)) a a'
    : τ (Functor (Hom_cat (Hom_cat B b b') a a')
      (Hom_cat (Hom_cat C (@fapp0 B C X b) (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P) D) b'))
        (@tapp1_fapp0 B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
          D) b b' (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z) a)
        (@tapp1_fapp0 B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
          D) b b' (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z) a')));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (b : τ
  (Obj B))
  ⊢ @tapp0_fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) b
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D
        (@one_cat_diagram_family_reconstruction_to B C C1 D) walking_arrow_src)
    ≡ @id C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (b : τ
  (Obj B))
  ⊢ @tapp0_fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) b
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D
        (@one_cat_diagram_family_reconstruction_to B C C1 D) walking_arrow_tgt)
    ≡ @id C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b);
