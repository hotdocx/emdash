require open emdash.emdash3_2_one_cat_image_kernel_exactness;

// The conditional construction certifies the actual original comparison.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (z : τ (@=
  (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A
  D h)) (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h) (@zero_arrow_family_zero_transf B C
  t T T0 (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D
  h)))) ⊢ @iso_evidence_to (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@omega_equiv_along_iso_evidence (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@one_cat_image_kernel_exact_from_boundary_zero B
  C S C1 t T T0 P Q A D h N z)) ≡ (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (z : τ (@=
  (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A
  D h)) (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h) (@zero_arrow_family_zero_transf B C
  t T T0 (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D
  h)))) ⊢ @omega_equiv_along_left_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
  (@one_cat_image_kernel_exact_from_boundary_zero B C S C1 t T T0 P Q A D h N z) : τ (@= (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@omega_equiv_along_left_inv (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@one_cat_image_kernel_exact_from_boundary_zero B
  C S C1 t T T0 P Q A D h N z)) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)) (@id (Functor_cat B
  C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h))));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (z : τ (@=
  (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A
  D h)) (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h) (@zero_arrow_family_zero_transf B C
  t T T0 (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D
  h)))) ⊢ @omega_equiv_left_as_right_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
  (@one_cat_image_kernel_exact_from_boundary_zero B C S C1 t T T0 P Q A D h N z) : τ (@= (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P D)) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
  (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N)
  (@one_cat_image_kernel_exact_from_boundary_zero B C S C1 t T T0 P Q A D h N z))) (@id (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D)));
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T
  : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0
  P Q)) (z : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B
  C S t T T0 P Q A D h)) (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h)
  (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q A D h)))) (other : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D))) ⊢ (@one_cat_image_kernel_exact_from_boundary_zero B
  C S C1 t T T0 P Q A D h N z) : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) other);

// An original short-exact row derives the condition through its original β equivalence.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (R : τ
  (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) ⊢ @iso_evidence_to (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func B C
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@omega_equiv_along_iso_evidence (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func B C t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N) (@one_cat_short_exact_image_kernel_omega B C S C1
  t T T0 P Q A D h N R)) ≡ (@one_cat_image_to_kernel_transf B C S C1 t T T0 P Q A D h N);
