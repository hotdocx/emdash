/* Primary ordinary family universality from the existing adjunction owner.
   J:p⊣t (respectively t⊣p) supplies the universal data. The optional whole
   arrow presentation e preserves an existing chosen family; it carries no
   separate naturality-square proof. The closed profile of Terminal_cat is
   used internally. All operations below are definitions; no universal
   structure or isomorphism witness is postulated here.

   Results retain actual whole maps and inverse maps as IsoEvidence. Their
   inverse laws are proved by the categorical owners, not asserted as new
   DefIso runtime cuts. The C1 guard qualifies ordinary diagram realization;
   no general weak higher-terminality theorem is claimed. */
require open emdash.emdash3_2_one_cat_adjunction_family_views;
require open emdash.emdash3_2_terminal_category_profile;
require open emdash.emdash3_2_one_cat_arrow_family_isomorphisms;
require open emdash.emdash3_2_one_cat_diagram_family_reconstruction;

// Whole Hom contraction through the original lifted adjunction and its inverse.
symbol one_cat_terminal_adjunction_family_hom_iso [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  : τ (@DefIso Cat_cat (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat)
≔ @defiso_sym Cat_cat Terminal_cat _
    (@adjunction_hom_component_iso (Functor_cat B C) (Functor_cat B Terminal_cat)
      (@comp_cat_cov_func B C Terminal_cat (Terminal_func C))
      (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t))
      (@one_cat_postcomp_adjunction B C Terminal_cat C1 terminal_category_one_cat
        (Terminal_func C) (@Obj_func C t) J) F (Terminal_func B));

// Lift the terminal arrow and its inverse as a whole invertible modification.
symbol one_cat_terminal_adjunction_family_modification_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  (h k : τ (@Transf B C F (@Const_func B C t)))
  : τ (IsoEvidence (Hom_cat (Functor_cat B C) F (@Const_func B C t)) h k)
≔ @iso_evidence_fmap Terminal_cat (Hom_cat (Functor_cat B C) F (@Const_func B C t)) (@defiso_from Cat_cat (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@one_cat_terminal_adjunction_family_hom_iso B C C1 t J F)) (@fapp0 (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@one_cat_terminal_adjunction_family_hom_iso B C C1 t J F)) h) (@fapp0 (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@one_cat_terminal_adjunction_family_hom_iso B C C1 t J F)) k)
    (@terminal_category_arrow_iso (@fapp0 (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@one_cat_terminal_adjunction_family_hom_iso B C C1 t J F)) h) (@fapp0 (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) F (@Const_func B C t)) Terminal_cat (@one_cat_terminal_adjunction_family_hom_iso B C C1 t J F)) k));

// Transparent presentation: retain e and F in the actual composed diagram.
symbol terminal_adjunction_presented_family [B C : Cat] [t : τ (Obj C)]
  (e : τ (@Transf C C (@id_func C) (@Const_func C C t))) (F : τ (Functor B C))
  : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func C C (@id_func C) (@Const_func C C t) e) F;

// Reach the chosen original diagram through the categorical reconstruction.
symbol one_cat_terminal_adjunction_family_presentation_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@id_func C) (@Const_func C C t))) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@terminal_adjunction_presented_family B C t e F))
≔ @iso_evidence_comp (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@transf_arrow_diagram_func B C F (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@terminal_adjunction_presented_family B C t e F)
    (@one_cat_diagram_family_reconstruction_evidence B C C1 (@terminal_adjunction_presented_family B C t e F))
    (@one_cat_arrow_family_comparison_evidence B C C1 F (@Const_func B C t) h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@one_cat_terminal_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@terminal_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// Default presentation uses the same adjunction's whole unit.
symbol one_cat_terminal_adjunction_family_normalization [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction C Terminal_cat (Terminal_func C) (@Obj_func C t))) (F : τ (Functor B C))
  (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F (@Const_func B C t) h) (@terminal_adjunction_presented_family B C t (@unit_adj_transf C Terminal_cat (Terminal_func C) (@Obj_func C t) J) F))
≔ @one_cat_terminal_adjunction_family_presentation_evidence B C C1 t J F (@unit_adj_transf C Terminal_cat (Terminal_func C) (@Obj_func C t) J) h;

// Whole Hom contraction through the original lifted adjunction and its inverse.
symbol one_cat_initial_adjunction_family_hom_iso [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  : τ (@DefIso Cat_cat (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat)
≔ @adjunction_hom_component_iso (Functor_cat B Terminal_cat) (Functor_cat B C)
    (@comp_cat_cov_func B Terminal_cat C (@Obj_func C t))
    (@comp_cat_cov_func B C Terminal_cat (Terminal_func C))
    (@one_cat_postcomp_adjunction B Terminal_cat C terminal_category_one_cat C1
      (@Obj_func C t) (Terminal_func C) J) (Terminal_func B) F;

// Lift the terminal arrow and its inverse as a whole invertible modification.
symbol one_cat_initial_adjunction_family_modification_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  (h k : τ (@Transf B C (@Const_func B C t) F))
  : τ (IsoEvidence (Hom_cat (Functor_cat B C) (@Const_func B C t) F) h k)
≔ @iso_evidence_fmap Terminal_cat (Hom_cat (Functor_cat B C) (@Const_func B C t) F) (@defiso_from Cat_cat (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@one_cat_initial_adjunction_family_hom_iso B C C1 t J F)) (@fapp0 (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@one_cat_initial_adjunction_family_hom_iso B C C1 t J F)) h) (@fapp0 (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@one_cat_initial_adjunction_family_hom_iso B C C1 t J F)) k)
    (@terminal_category_arrow_iso (@fapp0 (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@one_cat_initial_adjunction_family_hom_iso B C C1 t J F)) h) (@fapp0 (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@defiso_to Cat_cat (Hom_cat (Functor_cat B C) (@Const_func B C t) F) Terminal_cat (@one_cat_initial_adjunction_family_hom_iso B C C1 t J F)) k));

// Transparent presentation: retain e and F in the actual composed diagram.
symbol initial_adjunction_presented_family [B C : Cat] [t : τ (Obj C)]
  (e : τ (@Transf C C (@Const_func C C t) (@id_func C))) (F : τ (Functor B C))
  : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@transf_arrow_diagram_func C C (@Const_func C C t) (@id_func C) e) F;

// Reach the chosen original diagram through the categorical reconstruction.
symbol one_cat_initial_adjunction_family_presentation_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  (e : τ (@Transf C C (@Const_func C C t) (@id_func C))) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@initial_adjunction_presented_family B C t e F))
≔ @iso_evidence_comp (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@transf_arrow_diagram_func B C (@Const_func B C t) F (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@initial_adjunction_presented_family B C t e F)
    (@one_cat_diagram_family_reconstruction_evidence B C C1 (@initial_adjunction_presented_family B C t e F))
    (@one_cat_arrow_family_comparison_evidence B C C1 (@Const_func B C t) F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@one_cat_initial_adjunction_family_modification_evidence B C C1 t J F h (@diagram_family_transf B WalkingArrow_cat C (@initial_adjunction_presented_family B C t e F) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// Default presentation uses the same adjunction's whole counit.
symbol one_cat_initial_adjunction_family_normalization [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (J : τ (@Adjunction Terminal_cat C (@Obj_func C t) (Terminal_func C))) (F : τ (Functor B C))
  (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@Const_func B C t) F h) (@initial_adjunction_presented_family B C t (@counit_adj_transf Terminal_cat C (@Obj_func C t) (Terminal_func C) J) F))
≔ @one_cat_initial_adjunction_family_presentation_evidence B C C1 t J F (@counit_adj_transf Terminal_cat C (@Obj_func C t) (Terminal_func C) J) h;
