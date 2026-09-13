/* Whole original-family input reconstruction and retained endpoint action. */
require open emdash.emdash3_2_one_cat_cokernel_family_inputs;

// Reconstruction keeps the original whole src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@transf_arrow_diagram_func B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
    (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@one_cat_diagram_family_reconstruction_from B C C1 D) walking_arrow_src) ≡ @id (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src);

// Its identity endpoint retains the original parameter Hom action.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (b c : τ (Obj B)) ⊢ @tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b c (@sym_transf_tapp0_transf B
    WalkingArrow_cat C D (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
    WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@one_cat_diagram_family_reconstruction_from B C C1 D) walking_arrow_src) ≡ @fapp1_func B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b c;

// Reconstruction keeps the original whole tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@transf_arrow_diagram_func B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
    (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@one_cat_diagram_family_reconstruction_from B C C1 D) walking_arrow_tgt) ≡ @id (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt);

// Its identity endpoint retains the original parameter Hom action.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (b c : τ (Obj B)) ⊢ @tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c (@sym_transf_tapp0_transf B
    WalkingArrow_cat C D (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
    WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@one_cat_diagram_family_reconstruction_from B C C1 D) walking_arrow_tgt) ≡ @fapp1_func B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b c;

// The whole original-family input recovers the supplied u.
assert [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y)))
  ⊢ (@one_cat_cokernel_family_input_target_path B C C1 t T T0 D Y u z) : τ (@= (@Transf B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) Y) (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C
    (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) (@one_cat_cokernel_family_input B C C1 t
    T T0 D Y u z) walking_arrow_tgt) u);

// Reconstruction does not replace u by an unrelated transformation.
assertnot [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (v : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  ⊢ (@one_cat_cokernel_family_input_target_path B C C1 t T T0 D Y u z) : τ (@= (@Transf B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) Y) (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C
    (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) (@one_cat_cokernel_family_input B C C1 t
    T T0 D Y u z) walking_arrow_tgt) v);

// The retained target equation includes the entire off-diagonal Hom functor.
assert [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (b c : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (Functor (Hom_cat B b c)
    (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) b) (@fapp0 B C Y c))) (λ
    h : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y), (@tapp1_func B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y b c h)) (@sym_transf_tapp0_transf B
    WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)
    (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z) walking_arrow_tgt) u
    (@one_cat_cokernel_family_input_target_path B C C1 t T T0 D Y u z)
    : τ (@= (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) b) (@fapp0 B C Y c))) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_tgt) Y b c (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat
      WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) (@one_cat_cokernel_family_input B C C1 t T T0 D Y u
      z) walking_arrow_tgt)) (@tapp1_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y b c
      u));
