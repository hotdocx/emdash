/*
  Ordinary terminal/initial adjunction presentations of the existing choices.

  The two structural primitives supply !:C→1 ⊣ t:1→C and t:1→C ⊣ !:C→1.
  They are explicit extensions, not definitions derived from the old terminal
  beta rules. The C1 guard qualifies their computational DefIso-valued Hom
  comparison. This is not a general weak higher-adjunction construction.

  Units/counits and the whole Hom comparison remain owned by Adjunction.
  Existing ordinary family normalizers compare their diagram families to the
  original terminal/initial families, with identity endpoint components.
  No manual naturality-square data is required. In particular there is no
  rewrite identifying the new unit with terminal_arrow_transf: the original
  terminal component at t deliberately stays distinct from id_t at runtime.

  The derived Hom equivalences and ordinary contractions use these actual
  mates and retain their selected inverse, without equality-transport of a
  functor. General higher terminality remains a separate qualified boundary.
*/
require open emdash.emdash3_2_one_cat_terminal_family_universality;
require open emdash.emdash3_2_adjunction_mates;
require open emdash.emdash3_2_categorical_contractions;

// Explicit structural presentation of the selected ordinary terminal object.
injective symbol one_cat_terminal_adjunction [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t));

// Dual ordinary structural presentation; no unrestricted higher duality claim.
injective symbol one_cat_initial_adjunction [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C));

// Whole unit; its endpoint action stays with the generic adjunction calculus.
symbol one_cat_terminal_adjunction_unit [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  : τ (@Transf C C (@id_func C) (@Const_func C C t))
≔ @unit_adj_transf C Terminal_cat (Terminal_func C) (@Obj_func C t)
    (@one_cat_terminal_adjunction C C1 t T);

// Whole counit of the ordinary initial-object presentation.
symbol one_cat_initial_adjunction_counit [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  : τ (@Transf C C (@Const_func C C t) (@id_func C))
≔ @counit_adj_transf Terminal_cat C (@Obj_func C t) (Terminal_func C)
    (@one_cat_initial_adjunction C C1 t T);

// Categorical comparison with the original terminal-arrow family.
symbol one_cat_terminal_adjunction_diagram_iso [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  : τ (@DefIso (Functor_cat C (Functor_cat WalkingArrow_cat C))
      (@transf_arrow_diagram_func C C (@id_func C) (@Const_func C C t)
        (@one_cat_terminal_adjunction_unit C C1 t T))
      (@terminal_arrow_diagram_func C t T))
≔ @one_cat_terminal_arrow_family_iso C C C1 t T (@id_func C)
    (@one_cat_terminal_adjunction_unit C C1 t T);

// Categorical comparison with the original initial-arrow family.
symbol one_cat_initial_adjunction_diagram_iso [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  : τ (@DefIso (Functor_cat C (Functor_cat WalkingArrow_cat C))
      (@transf_arrow_diagram_func C C (@Const_func C C t) (@id_func C)
        (@one_cat_initial_adjunction_counit C C1 t T))
      (@initial_arrow_diagram_func C t T))
≔ @one_cat_initial_arrow_family_iso C C C1 t T (@id_func C)
    (@one_cat_initial_adjunction_counit C C1 t T);

// Evaluation of the whole adjunction comparison at (x,*), with reversed orientation.
symbol one_cat_terminal_hom_iso [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (x : τ (Obj C))
  : τ (@DefIso Cat_cat (Hom_cat C x t) Terminal_cat)
≔ @defiso_sym Cat_cat Terminal_cat (Hom_cat C x t)
    (@adjunction_hom_component_iso C Terminal_cat (Terminal_func C) (@Obj_func C t)
      (@one_cat_terminal_adjunction C C1 t T) x Terminal_obj);

// Evaluation of the dual whole adjunction comparison at (*,x).
symbol one_cat_initial_hom_iso [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C))
  : τ (@DefIso Cat_cat (Hom_cat C t x) Terminal_cat)
≔ @adjunction_hom_component_iso Terminal_cat C (@Obj_func C t) (Terminal_func C)
    (@one_cat_initial_adjunction C C1 t T) Terminal_obj x;

// Retain the actual selected Hom mate and both inverse slots.
symbol one_cat_terminal_hom_equivalence [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (x : τ (Obj C))
  : τ (@OmegaEquivAlong Cat_cat (Hom_cat C x t) Terminal_cat
      (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x)))
≔ @iso_evidence_omega_along Cat_cat (Hom_cat C x t) Terminal_cat
    (@defiso_iso_evidence Cat_cat (Hom_cat C x t) Terminal_cat
      (@one_cat_terminal_hom_iso C C1 t T x));

// Object/core uniqueness is a derived observation of the categorical data.
symbol one_cat_terminal_hom_contraction [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (x : τ (Obj C))
  : τ (IsContr (Obj (Hom_cat C x t)))
≔ @cat_contraction_objects_along (Hom_cat C x t)
    (@defiso_to Cat_cat (Hom_cat C x t) Terminal_cat (@one_cat_terminal_hom_iso C C1 t T x))
    (@one_cat_terminal_hom_equivalence C C1 t T x);

// Retain the actual selected Hom mate and both inverse slots.
symbol one_cat_initial_hom_equivalence [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C))
  : τ (@OmegaEquivAlong Cat_cat (Hom_cat C t x) Terminal_cat
      (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x)))
≔ @iso_evidence_omega_along Cat_cat (Hom_cat C t x) Terminal_cat
    (@defiso_iso_evidence Cat_cat (Hom_cat C t x) Terminal_cat
      (@one_cat_initial_hom_iso C C1 t T x));

// Object/core uniqueness is a derived observation of the categorical data.
symbol one_cat_initial_hom_contraction [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C))
  : τ (IsContr (Obj (Hom_cat C t x)))
≔ @cat_contraction_objects_along (Hom_cat C t x)
    (@defiso_to Cat_cat (Hom_cat C t x) Terminal_cat (@one_cat_initial_hom_iso C C1 t T x))
    (@one_cat_initial_hom_equivalence C C1 t T x);
