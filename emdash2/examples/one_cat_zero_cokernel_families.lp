require open emdash.emdash3_2_one_cat_zero_cokernel_families;

// The same original Q descent supplies the inverse, with no new inverse choice.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ @omega_equiv_along_left_inv (Functor_cat
  B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S
  t T0 Q D) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@one_cat_zero_cokernel_omega B C S C1
  t T T0 Q D z) ≡ (@one_cat_zero_cokernel_retraction B C S C1 t T T0 Q D z);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ @one_cat_zero_cokernel_left_path B C S
  C1 t T T0 Q D z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_zero_cokernel_retraction B C S
  C1 t T T0 Q D z) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@id (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ
  (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) ⊢ @one_cat_zero_cokernel_right_path B C S
  C1 t T T0 Q D z : τ (@= (@Transf B C (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@cokernel_adjunction_family_func B C S t T0 Q D)) (@comp_fapp0 (Functor_cat B C)
  (@cokernel_adjunction_family_func B C S t T0 Q D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0 Q D)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@one_cat_zero_cokernel_retraction B C S C1 t T
  T0 Q D z)) (@id (Functor_cat B C) (@cokernel_adjunction_family_func B C S t T0 Q D)));
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T
  : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t
  T0)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))) (other : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D))) ⊢ (@one_cat_zero_cokernel_omega B C S C1 t T T0 Q D z) : τ (@OmegaEquivAlong (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D) other);
