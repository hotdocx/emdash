/* Descent at the same original Q(D), through whole native mates. */
require open emdash.emdash3_2_one_cat_cokernel_family_descent;
require open emdash.emdash3_2_one_cat_adjunction_family_views;
require open emdash.emdash3_2_cokernel_adjunction_families;

// Optional raw formula, derived from the original whole native mate.
symbol review_cokernel_descent_raw_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y)))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)
    Y) (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) (@cokernel_adjunction_family_colift_transf B C S t
    T0 Q D Y (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z)))
≔ @one_cat_adjunction_family_untranspose_agrees B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y
      (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z);

// Native inverse mating recovers the complete coherent input.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y)))
  ⊢ @fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y)
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) ≡ (@one_cat_cokernel_family_input B C C1 t T T0 D Y u
    z);

// The complete input is not replaced by an unrelated one.
assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (other : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat
        WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y)))
  ⊢ @fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y)
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) ≡ other;

// Whole reconstruction recovers the supplied transformation.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y)))
  ⊢ @one_cat_cokernel_family_descent_reconstruction B C S C1 t T T0 Q D Y u z : τ (@= (@Transf B C
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@sym_transf_tapp0_transf B WalkingArrow_cat
    C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) (@fapp0 _ _
    (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
    WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
    (@cokernel_adjunction_evidence C S t T0 Q) D Y) (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z))
    walking_arrow_tgt) u);

// Descent is unique with this same whole reconstruction.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (b : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S
        t T0 Q) D) Y)) (p : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
        (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) Y) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
        WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
        Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) b) walking_arrow_tgt)
        u))
  ⊢ @one_cat_cokernel_family_descent_unique B C S C1 t T T0 Q D Y u z b p : τ (@= (@Transf B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y) b
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z));

// The component starts at Q of the original D(b).
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y
    b (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C)
    C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y b));

// The native/raw whole agreement retains component.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (b : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    D) Y) (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B
    (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y b)) (λ w : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y), (@tapp0_fapp0 B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b w))
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) (@cokernel_adjunction_family_colift_transf B C S t T0
    Q D Y (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z)) (@review_cokernel_descent_raw_path B C S C1 t T T0 Q
    D Y u z) : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0
    B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y b)) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b (@one_cat_cokernel_family_descent B C S C1 t T
    T0 Q D Y u z)) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func
    C S t T0 Q) D) Y b (@cokernel_adjunction_family_colift_transf B C S t T0 Q D Y (@one_cat_cokernel_family_input B C
    C1 t T T0 D Y u z))));

// The native/raw whole agreement retains whole Hom action.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (b c : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    D) Y) (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
    S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c))) (λ w : τ (@Transf B C
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y), (@tapp1_func B
    C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b c w))
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) (@cokernel_adjunction_family_colift_transf B C S t T0
    Q D Y (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z)) (@review_cokernel_descent_raw_path B C S C1 t T T0 Q
    D Y u z) : τ (@= (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c)))
    (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y
    b c (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b c (@cokernel_adjunction_family_colift_transf B
    C S t T0 Q D Y (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z))));

// The native/raw whole agreement retains an arbitrary base arrow.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (b c : τ (Obj B)) (m : τ (Hom B b c))
  ⊢ @eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    D) Y) (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B
    (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c)) (λ w : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y), (@tapp1_fapp0 B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b c w m))
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z) (@cokernel_adjunction_family_colift_transf B C S t T0
    Q D Y (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z)) (@review_cokernel_descent_raw_path B C S C1 t T T0 Q
    D Y u z) : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0
    B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c)) (@tapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b c (@one_cat_cokernel_family_descent B C S C1 t
    T T0 Q D Y u z) m) (@tapp1_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c (@cokernel_adjunction_family_colift_transf B C S t T0 Q D Y
    (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z)) m));

// The native/raw whole agreement retains the next Hom functor with both retained endpoints.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y))) (b c : τ (Obj B)) (m n : τ (Hom B b c))
  ⊢ @eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    D) Y) (Obj (@LaxArrow_cat Cat_cat)) (λ w : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y), (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) m n) (Hom_cat (Hom_cat C
    (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat
    WalkingArrow_cat C) D b)) (@fapp0 B C Y c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
    (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c w) m) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
    (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c w) n)) (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat
    C) D b)) (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c w) m n))) (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y
    u z) (@cokernel_adjunction_family_colift_transf B C S t T0 Q D Y (@one_cat_cokernel_family_input B C C1 t T T0 D Y
    u z)) (@review_cokernel_descent_raw_path B C S C1 t T T0 Q D Y u z) : τ (@= (Obj (@LaxArrow_cat Cat_cat))
    (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) m n) (Hom_cat (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c)) (@fapp0
    (Hom_cat B b c) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b c
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) m) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat
    C) D b)) (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) n))
    (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S
    t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y b c
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) m n)) (@lax_edge Cat_cat (Hom_cat (Hom_cat B b c) m
    n) (Hom_cat (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B
    (Functor_cat WalkingArrow_cat C) D b)) (@fapp0 B C Y c)) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
    (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c (@cokernel_adjunction_family_colift_transf B C S t T0 Q D Y
    (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z))) m) (@fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat
    C) D b)) (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c (@cokernel_adjunction_family_colift_transf B C S t T0 Q D Y
    (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z))) n)) (@fapp1_func (Hom_cat B b c) (Hom_cat C (@fapp0
    (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat
    C) D b)) (@fapp0 B C Y c)) (@tapp1_func B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) D) Y b c (@cokernel_adjunction_family_colift_transf B C S t T0 Q D Y
    (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z))) m n)));
