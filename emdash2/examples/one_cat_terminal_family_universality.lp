/* Whole terminal/initial family normalizers: endpoints, inverse cuts,
   retained higher action, and the required zero-endpoint premise. */
require open emdash.emdash3_2_one_cat_terminal_family_universality;

// terminal to fixes the src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)))
    ≡ @id C (@fapp0 B C F b);

// terminal to fixes the tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)))
    ≡ @id C t;

// terminal from fixes the src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)))
    ≡ @id C (@fapp0 B C F b);

// terminal from fixes the tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)))
    ≡ @id C t;

// Whole inverse cancellation at the original source family.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t)))
  ⊢ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h))
    ≡ @id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h);

// Whole inverse cancellation at the original target family.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t)))
  ⊢ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h))
    ≡ @id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F);

// A further Hom of the whole comparison remains available.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t))) (x y : τ (Obj B)) (p q : τ (Hom B x y))
  ⊢ @fapp1_func _ _ (@tapp1_func B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) x y (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h))) p q
    : τ (Functor (Hom_cat (Hom_cat B x y) p q)
      (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) x) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) y))
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) x y (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) p)
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) x y (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) q)));

// An unrelated endpoint family cannot replace the required constant zero end.
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (G : τ (Functor B C)) (h : τ (@Transf B C F G))
  ⊢ @one_cat_terminal_arrow_family_iso B C C1 t T F h
    : τ (@DefIso (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@transf_arrow_diagram_func B C F G h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F));

// initial to fixes the src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)))
    ≡ @id C t;

// initial to fixes the tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)))
    ≡ @id C (@fapp0 B C F b);

// initial from fixes the src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)))
    ≡ @id C t;

// initial from fixes the tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) _ _ b (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)))
    ≡ @id C (@fapp0 B C F b);

// Whole inverse cancellation at the original source family.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F))
  ⊢ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)) (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h))
    ≡ @id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h);

// Whole inverse cancellation at the original target family.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F))
  ⊢ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)) (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h))
    ≡ @id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F);

// A further Hom of the whole comparison remains available.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F)) (x y : τ (Obj B)) (p q : τ (Hom B x y))
  ⊢ @fapp1_func _ _ (@tapp1_func B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) x y (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h))) p q
    : τ (Functor (Hom_cat (Hom_cat B x y) p q)
      (Hom_cat (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) x) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) y))
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) x y (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)) p)
        (@tapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) x y (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)) q)));

// An unrelated endpoint family cannot replace the required constant zero end.
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (G : τ (Functor B C)) (h : τ (@Transf B C G F))
  ⊢ @one_cat_initial_arrow_family_iso B C C1 t T F h
    : τ (@DefIso (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@transf_arrow_diagram_func B C G F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F));


// terminal to, whole src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h))
    walking_arrow_src) ≡ @id (Functor_cat B C) F;
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C F F b (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func
    B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@defiso_to
    _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) walking_arrow_src)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) b (@defiso_to _ _
        _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)));
// Further action is the original endpoint functor's Hom action.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b c : τ (Obj B))
  ⊢ @tapp1_func B C F F b c (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F
    (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
    (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) walking_arrow_src)
    ≡ @fapp1_func B C F b c;
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (other : τ (@Transf B C F F))
  ⊢ eq_refl (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@defiso_to _ _ _
    (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) walking_arrow_src) : τ (@= (@Transf B C F F)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@defiso_to _ _ _
    (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) walking_arrow_src) other);

// terminal to, whole tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h))
    walking_arrow_tgt) ≡ @id (Functor_cat B C) (@Const_func B C t);
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@Const_func B C t) (@Const_func B C t) b (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h))
    walking_arrow_tgt)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) b (@defiso_to _ _
        _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)));

// terminal from, whole src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C
    C1 t T F h)) walking_arrow_src) ≡ @id (Functor_cat B C) F;
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C F F b (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
    (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)) walking_arrow_src)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) b (@defiso_from
        _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)));

// terminal from, whole tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C
    C1 t T F h)) walking_arrow_tgt) ≡ @id (Functor_cat B C) (@Const_func B C t);
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@Const_func B C t) (@Const_func B C t) b (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C
    C1 t T F h)) walking_arrow_tgt)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) b (@defiso_from
        _ _ _ (@one_cat_terminal_arrow_family_iso B C C1 t T F h)));
// Further action is the original endpoint functor's Hom action.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t))) (b c : τ (Obj B))
  ⊢ @tapp1_func B C (@Const_func B C t) (@Const_func B C t) b c (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F)
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso B C
    C1 t T F h)) walking_arrow_tgt)
    ≡ @fapp1_func B C (@Const_func B C t) b c;

// initial to, whole src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h))
    walking_arrow_src) ≡ @id (Functor_cat B C) (@Const_func B C t);
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@Const_func B C t) (@Const_func B C t) b (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h))
    walking_arrow_src)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) b (@defiso_to _ _ _
        (@one_cat_initial_arrow_family_iso B C C1 t T F h)));

// initial to, whole tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T) F) (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h))
    walking_arrow_tgt) ≡ @id (Functor_cat B C) F;
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C F F b (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B
    C t) F h) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@defiso_to _
    _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)) walking_arrow_tgt)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) b (@defiso_to _ _ _
        (@one_cat_initial_arrow_family_iso B C C1 t T F h)));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (other : τ (@Transf B C F F))
  ⊢ eq_refl (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@defiso_to _ _ _
    (@one_cat_initial_arrow_family_iso B C C1 t T F h)) walking_arrow_tgt) : τ (@= (@Transf B C F F)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@defiso_to _ _ _
    (@one_cat_initial_arrow_family_iso B C C1 t T F h)) walking_arrow_tgt) other);

// initial from, whole src endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C
    C1 t T F h)) walking_arrow_src) ≡ @id (Functor_cat B C) (@Const_func B C t);
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@Const_func B C t) (@Const_func B C t) b (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C
    C1 t T F h)) walking_arrow_src)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) b (@defiso_from
        _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)));

// initial from, whole tgt endpoint.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) ⊢ (@sym_transf_tapp0_transf B WalkingArrow_cat C
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F)
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C
    C1 t T F h)) walking_arrow_tgt) ≡ @id (Functor_cat B C) F;
// Both typed component orders meet at the same endpoint identity.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C F F b (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
    (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)) walking_arrow_tgt)
    ≡ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) b (@defiso_from
        _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)));
// Further action is the original endpoint functor's Hom action.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F)) (b c : τ (Obj B))
  ⊢ @tapp1_func B C F F b c (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F) (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
    (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso B C C1 t T F h)) walking_arrow_tgt)
    ≡ @fapp1_func B C F b c;
