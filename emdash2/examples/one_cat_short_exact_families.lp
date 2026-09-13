/* Whole kernel-cokernel pair, retained comparisons and inverse action. */
require open emdash.emdash3_2_one_cat_short_exact_families;
require open emdash.emdash3_2_eq1_evidence_property;

// Constructor projections retain both original fixed-map witnesses.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (k : τ (@OmegaEquivAlong (Functor_cat B C) A
    (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h))) (q
    : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)))
  ⊢ @one_cat_short_exact_family_kernel_equiv B C S C1 t T T0 P Q A D h (@one_cat_short_exact_family_intro B C S C1 t T T0 P Q A D h k q)
    ≡ k;

// The cokernel witness is the original one.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (k : τ (@OmegaEquivAlong (Functor_cat B C) A
    (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h))) (q
    : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)))
  ⊢ @one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h (@one_cat_short_exact_family_intro B C S C1 t T T0 P Q A D h k
    q) ≡ q;

// The selected kernel inverse is whole and has the original target.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  ⊢ (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R) : τ (@Transf B C (@kernel_adjunction_family_func B
    C S t T P D) A);

// Its first inverse law is the existing fixed-map law.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  ⊢ @omega_equiv_along_left_law (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T T0 P Q
    A D h R) : τ (@= (@Transf B C A A) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
    A (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R) (@kernel_adjunction_family_boundary_transf B C S
    t T P A D h)) (@id (Functor_cat B C) A));

// The same selected inverse also satisfies the other law.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  ⊢ @omega_equiv_left_as_right_law (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T T0 P Q
    A D h R) : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S
    t T P D)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) A
    (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
    (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R)) (@id (Functor_cat B C)
    (@kernel_adjunction_family_func B C S t T P D)));

// Whole kernel evidence projects to the actual component.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (b : τ
    (Obj B))
  ⊢ @omega_equiv_along_fapp1_fapp0 (Functor_cat B C) C (@fapp0_func B C b) A (@kernel_adjunction_family_func B C S t T
    P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T
    T0 P Q A D h R) : τ (@OmegaEquivAlong C (@fapp0 B C A b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P
    D) b) (@tapp0_fapp0 B C A (@kernel_adjunction_family_func B C S t T P D) b
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h)));

// The kernel inverse retains its full off-diagonal Hom action.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (b c : τ
    (Obj B))
  ⊢ @tapp1_func B C (@kernel_adjunction_family_func B C S t T P D) A b c (@one_cat_short_exact_family_kernel_inverse B C S C1 t
    T T0 P Q A D h R) ≡ @tapp1_func B C (@kernel_adjunction_family_func B C S t T P D) A b c
    (@omega_equiv_along_left_inv (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T T0 P Q
    A D h R));

// Its next Hom projection stays in that same whole inverse.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (b c : τ
    (Obj B)) (m n : τ (Hom B b c))
  ⊢ @fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) b) (@fapp0 B C A
    c)) (@tapp1_func B C (@kernel_adjunction_family_func B C S t T P D) A b c (@one_cat_short_exact_family_kernel_inverse B C S
    C1 t T T0 P Q A D h R)) m n ≡ @fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@kernel_adjunction_family_func B
    C S t T P D) b) (@fapp0 B C A c)) (@tapp1_func B C (@kernel_adjunction_family_func B C S t T P D) A b c
    (@omega_equiv_along_left_inv (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T T0 P Q
    A D h R))) m n;

// The selected cokernel inverse is whole and has the original target.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  ⊢ (@one_cat_short_exact_family_cokernel_inverse B C S C1 t T T0 P Q A D h R) : τ (@Transf B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)));

// Its first inverse law is the existing fixed-map law.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  ⊢ @omega_equiv_along_left_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
    (@one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h R) : τ (@= (@Transf B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t
    T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@zero_arrow_family_incoming_func B C t T A D h))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@one_cat_short_exact_family_cokernel_inverse B C S C1 t T T0 P Q A D h R) (@one_cat_row_cokernel_comparison B C S C1 t T T0
    Q A D h)) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func
    C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))));

// The same selected inverse also satisfies the other law.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  ⊢ @omega_equiv_left_as_right_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
    (@one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h R) : τ (@= (@Transf B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
    (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C
    S C1 t T T0 Q A D h) (@one_cat_short_exact_family_cokernel_inverse B C S C1 t T T0 P Q A D h R)) (@id (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)));

// Whole cokernel evidence projects to the actual component.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (b : τ
    (Obj B))
  ⊢ @omega_equiv_along_fapp1_fapp0 (Functor_cat B C) C (@fapp0_func B C b) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0
    Q A D h) (@one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h R) : τ (@OmegaEquivAlong C (@fapp0 B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) b) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) b (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)));

// The cokernel inverse retains its full off-diagonal Hom action.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (b c : τ
    (Obj B))
  ⊢ @tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) b c
    (@one_cat_short_exact_family_cokernel_inverse B C S C1 t T T0 P Q A D h R) ≡ @tapp1_func B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) b c
    (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
    (@one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h R));

// Its next Hom projection stays in that same whole inverse.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (b c : τ
    (Obj B)) (m n : τ (Hom B b c))
  ⊢ @fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) b) (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func
    C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) c)) (@tapp1_func B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) b c
    (@one_cat_short_exact_family_cokernel_inverse B C S C1 t T T0 P Q A D h R)) m n ≡ @fapp1_func (Hom_cat B b c) (Hom_cat C
    (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b) (@fapp0 B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t
    T A D h)) c)) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0
    B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C
    t T A D h)) b c (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
    C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0
    Q A D h) (@one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h R))) m n;

// A witness on an unrelated kernel-valued map cannot certify the actual β.
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)))
    (kb : τ (@OmegaEquivAlong (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D) b)) (q : τ
    (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)))
  ⊢ @one_cat_short_exact_family_intro B C S C1 t T T0 P Q A D h kb q : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h);

// A witness on an unrelated cokernel-valued map cannot certify the actual γ.
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
    C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h))
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) (k : τ (@OmegaEquivAlong (Functor_cat B C) A
    (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_boundary_transf B C S t T P A D h))) (qb
    : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) b))
  ⊢ @one_cat_short_exact_family_intro B C S C1 t T T0 P Q A D h k qb : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h);

// The cokernel comparison inverse is not a chosen section into the middle term.
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  ⊢ (@one_cat_short_exact_family_cokernel_inverse B C S C1 t T T0 P Q A D h R) : τ (@Transf B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src));

// Native inverse mating recovers the entire original row comparison input.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  ⊢ @fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@zero_arrow_family_incoming_func
    B C t T A D h) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@one_cat_row_cokernel_comparison
    B C S C1 t T T0 Q A D h) ≡ (@one_cat_cokernel_family_input B C C1 t T T0 (@zero_arrow_family_incoming_func B C t T
    A D h) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
    WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_zero_family_chain_path B C C1 t T
    T0 A D h));

// Its whole target reconstructs the original outgoing differential.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  ⊢ @one_cat_row_cokernel_reconstruction_path B C S C1 t T T0 Q A D h : τ (@= (@Transf B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t T A D h) (@comp_cat_fapp0 B
    C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@zero_arrow_family_incoming_func
    B C t T A D h) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@one_cat_row_cokernel_comparison
    B C S C1 t T T0 Q A D h)) walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator));

// The actual component keeps Q of the original incoming diagram.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) b (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
    : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B
      (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func B C t T A D h) b))
      (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt));

// Native reconstruction retains its entire parameter Hom action.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt)) (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) c))) (λ z : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)), (@tapp1_func B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c z))
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t T A D h) (@comp_cat_fapp0 B
    C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@zero_arrow_family_incoming_func
    B C t T A D h) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
    (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)) walking_arrow_tgt) (@diagram_family_transf B
    WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_row_cokernel_reconstruction_path B C S C1 t T T0 Q A D h)
    : τ (@= (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) c)))
      (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt) b c (@sym_transf_tapp0_transf B WalkingArrow_cat C
      (@zero_arrow_family_incoming_func B C t T A D h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0
      _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
      WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@one_cat_row_cokernel_comparison B C S C1 t
      T T0 Q A D h)) walking_arrow_tgt)) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// The next Hom functor keeps both dependent endpoints in the existing native arrow carrier.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p q : τ (Hom B b c))
  ⊢ @eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt)) (Obj (@LaxArrow_cat Cat_cat)) (λ z : τ (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt)), (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) p q) (Hom_cat (Hom_cat C (@fapp0 B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) c)) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c z) p) (@fapp0 (Hom_cat B
    b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) c)) (@tapp1_func B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c z)
    q)) (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) c))
    (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) b c z) p q))) (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@zero_arrow_family_incoming_func B C t T A D h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0 _
    _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
    WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
    (@cokernel_adjunction_evidence C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@one_cat_row_cokernel_comparison B C S C1 t T
    T0 Q A D h)) walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) (@one_cat_row_cokernel_reconstruction_path B C S C1 t T T0 Q A D h)
    : τ (@= (Obj (@LaxArrow_cat Cat_cat)) (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) p q) (Hom_cat (Hom_cat C (@fapp0
      B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt) c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt) c)) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t T A D h) (@comp_cat_fapp0
      B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
      Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)
      (@zero_arrow_family_incoming_func B C t T A D h) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt)) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)) walking_arrow_tgt)) p) (@fapp0
      (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b)
      (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) c)) (@tapp1_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
      D walking_arrow_tgt) b c (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t
      T A D h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0 _ _
      (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
      WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@one_cat_row_cokernel_comparison B C S C1 t
      T T0 Q A D h)) walking_arrow_tgt)) q)) (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt) c)) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t T A D h) (@comp_cat_fapp0
      B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
      Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)
      (@zero_arrow_family_incoming_func B C t T A D h) (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt)) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)) walking_arrow_tgt)) p q))
      (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) p q) (Hom_cat (Hom_cat C (@fapp0 B C (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) c)) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c (@diagram_family_transf B
      WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) p) (@fapp0 (Hom_cat B b c)
      (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b) (@fapp0 B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) c)) (@tapp1_func B C (@diagram_family_at_func
      B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) q))
      (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) b) (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) c))
      (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_tgt) b c (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
      walking_arrow_tgt walking_arrow_generator)) p q)));
