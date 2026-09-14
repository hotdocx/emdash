require open emdash.emdash3_2_one_cat_coimage_cover_descent;

// The original cover inverse recovers the original quotient of the kernel.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (E : τ
  (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) ⊢ @one_cat_coimage_cover_inverse_factor_path B C S
  C1 t T T0 P Q D E : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)) (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C)
  C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E) (@diagram_family_transf B
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)));
// Whole descent reconstructs an independently supplied whole input.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (E : τ
  (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) (V : τ (Functor B C)) (u : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V)) (z : τ (@= (@Transf B C (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V u
  (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@zero_arrow_family_zero_transf B C t T T0
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V))) ⊢
  (@one_cat_coimage_cover_descent_reconstruction B C S C1 t T T0 P Q D E V u z) : τ (@= (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) V (@one_cat_coimage_cover_descent B C S C1 t T T0 P Q D E V u z) (@diagram_family_transf B
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) u);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (E : τ
  (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) (V : τ (Functor B C)) (u v : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V)) (p : τ (@= (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) V u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V v
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))) ⊢
  @one_cat_coimage_cover_reflect_path B C S C1 t T T0 P Q D E V u v p : τ (@= (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V) u v);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q :
  τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (E : τ
  (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) (V : τ (Functor B C)) (u : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V)) (z : τ (@= (@Transf B C (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V u
  (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@zero_arrow_family_zero_transf B C t T T0
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V))) (i j : τ (Obj
  B)) ⊢ @eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V) (Functor
  (Hom_cat B i j) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) i)
  (@fapp0 B C V j))) (λ h : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V),
  @tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V i j h) (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) V (@one_cat_coimage_cover_descent B C S C1 t T T0 P Q D E V u z)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) u
  (@one_cat_coimage_cover_descent_reconstruction B C S C1 t T T0 P Q D E V u z) : τ (@= (Functor (Hom_cat B i j)
  (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) i) (@fapp0 B C V j)))
  (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V i j (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) V (@one_cat_coimage_cover_descent B C S C1 t T T0 P Q D E V u z)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V i j u));
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T
  : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (E : τ
  (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) (other : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt))) ⊢ E : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) other);
