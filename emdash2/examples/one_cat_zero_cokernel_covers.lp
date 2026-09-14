require open emdash.emdash3_2_one_cat_zero_cokernel_covers;

// The chosen inverse is precisely the original kernel mate applied to id.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (D :
  τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ @omega_equiv_along_left_inv (Functor_cat
  B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P D) (@one_cat_zero_kernel_omega B C S C1 t T T0 P D z) ≡ (@one_cat_zero_kernel_section B C S C1 t T T0
  P D z);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (D :
  τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ @omega_equiv_along_left_law (Functor_cat
  B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P D) (@one_cat_zero_kernel_omega B C S C1 t T T0 P D z) : τ (@= (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@one_cat_zero_kernel_section B C S C1 t T T0 P D z)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (D :
  τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ @omega_equiv_left_as_right_law
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P D) (@one_cat_zero_kernel_omega B C S C1 t T T0 P D z) : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B
  C S t T P D) (@one_cat_zero_kernel_section B C S C1 t T T0 P D z)) (@id (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)));

// Both inverse laws belong to the actual existing coimage-to-target map.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)))) ⊢
  @iso_evidence_to (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@omega_equiv_along_iso_evidence (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@one_cat_zero_cokernel_cover_omega B C S C1 t T T0 P
  Q N D z)) ≡ (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)))) ⊢
  @omega_equiv_along_left_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@one_cat_zero_cokernel_cover_omega B C S C1 t T T0 P
  Q N D z) : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  S t T T0 P Q) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  D)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@one_cat_zero_cokernel_cover_omega B C S C1 t T T0 P
  Q N D z)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func
  C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)))) ⊢
  @omega_equiv_left_as_right_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@one_cat_zero_cokernel_cover_omega B C S C1 t T T0 P
  Q N D z) : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@omega_equiv_along_left_inv (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))
  (@one_cat_zero_cokernel_cover_omega B C S C1 t T T0 P Q N D z))) (@id (Functor_cat B C) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)))) (i j : τ (Obj
  B)) ⊢ @tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) i j (@omega_equiv_along_left_inv
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))
  (@one_cat_zero_cokernel_cover_omega B C S C1 t T T0 P Q N D z)) : τ (Functor (Hom_cat B i j) (Hom_cat C (@fapp0
  B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) i) (@fapp0 B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) j)));
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T
  : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)))) (other : τ
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) ⊢ (@one_cat_zero_cokernel_cover_omega B C S
  C1 t T T0 P Q N D z) : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) other);
