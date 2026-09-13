/* Incoming observations use the original whole test before any K/Q selection. */
require open emdash.emdash3_2_zero_arrow_family_observations;

assert [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b
    (@zero_arrow_family_incoming_transf B C t T A D h) ≡ (@tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
    (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) A) D b h));

assert [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B))
  ⊢ @fapp1_fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) (@zero_arrow_family_incoming_func B C t
    T A D h) b) walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ (@tapp0_fapp0 WalkingArrow_cat C _ _
    walking_arrow_src (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) A) D b h));

assert [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_family_incoming_func B C t T A D h) b c p) ≡ @fapp1_fapp0 B C A b c p;

assert [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_family_incoming_func B C t T A D h) b c p) ≡ @fapp1_fapp0 B C (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src) b c p;

assert [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B))
  ⊢ @tapp1_func B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b c (@diagram_family_transf B
    WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t T A D h) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) ≡ @tapp1_func B C A (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) b
    c (@zero_arrow_family_incoming_transf B C t T A D h);

assertnot [B C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (v : τ (@Transf B C A (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)))
  ⊢ @diagram_family_transf B WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t T A D h) walking_arrow_src
    walking_arrow_tgt walking_arrow_generator ≡ v;
