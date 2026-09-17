/* Derived whole arrow-family isomorphism from an invertible modification.
   All parameter action is in existing whole maps. The original inverse is
   retained; ordinary diagram reflection supplies the inverse-law evidence. */
require open emdash.emdash3_2_one_cat_diagram_family_reflection;
require open emdash.emdash3_2_one_cat_arrow_diagrams;

// Whole diagram action on the selected to modification.
symbol one_cat_arrow_family_comparison_to [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k))
≔ @sym_func_func_transf WalkingArrow_cat B C
    (@walking_arrow_func (Functor_cat B C) F G h)
    (@walking_arrow_func (Functor_cat B C) F G k)
    (@one_cat_square_diagram_transf (Functor_cat B C) (@one_cat_functor_category B C C1)
      F F G G h k (@id (Functor_cat B C) F) (@id (Functor_cat B C) G)
      (@iso_evidence_to (Hom_cat (Functor_cat B C) F G) h k i));

// Whole diagram action on the selected from modification.
symbol one_cat_arrow_family_comparison_from [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h))
≔ @sym_func_func_transf WalkingArrow_cat B C
    (@walking_arrow_func (Functor_cat B C) F G k)
    (@walking_arrow_func (Functor_cat B C) F G h)
    (@one_cat_square_diagram_transf (Functor_cat B C) (@one_cat_functor_category B C C1)
      F F G G k h (@id (Functor_cat B C) F) (@id (Functor_cat B C) G)
      (@iso_evidence_from (Hom_cat (Functor_cat B C) F G) h k i));

// The endpoints are identities; use existing whole-map reflection.
symbol one_cat_arrow_family_comparison_left_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k))
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@one_cat_arrow_family_comparison_from B C C1 F G h k i) (@one_cat_arrow_family_comparison_to B C C1 F G h k i)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h)))
≔ @one_cat_diagram_family_map_path B C C1 (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@one_cat_arrow_family_comparison_from B C C1 F G h k i) (@one_cat_arrow_family_comparison_to B C C1 F G h k i)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h))
    (@eq_trans (@Transf B C F F) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@one_cat_arrow_family_comparison_from B C C1 F G h k i) (@one_cat_arrow_family_comparison_to B C C1 F G h k i)) walking_arrow_src) (@id (Functor_cat B C) F) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h)) walking_arrow_src)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@one_cat_arrow_family_comparison_from B C C1 F G h k i) (@one_cat_arrow_family_comparison_to B C C1 F G h k i))
      (@eq_sym (@Transf B C F F) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h)) walking_arrow_src) (@id (Functor_cat B C) F) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@transf_arrow_diagram_func B C F G h))))
    (@eq_trans (@Transf B C G G) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@one_cat_arrow_family_comparison_from B C C1 F G h k i) (@one_cat_arrow_family_comparison_to B C C1 F G h k i)) walking_arrow_tgt) (@id (Functor_cat B C) G) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h)) walking_arrow_tgt)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@one_cat_arrow_family_comparison_from B C C1 F G h k i) (@one_cat_arrow_family_comparison_to B C C1 F G h k i))
      (@eq_sym (@Transf B C G G) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G h) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h)) walking_arrow_tgt) (@id (Functor_cat B C) G) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@transf_arrow_diagram_func B C F G h))));

// The endpoints are identities; use existing whole-map reflection.
symbol one_cat_arrow_family_comparison_right_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k))
  : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_to B C C1 F G h k i) (@one_cat_arrow_family_comparison_from B C C1 F G h k i)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k)))
≔ @one_cat_diagram_family_map_path B C C1 (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_to B C C1 F G h k i) (@one_cat_arrow_family_comparison_from B C C1 F G h k i)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k))
    (@eq_trans (@Transf B C F F) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_to B C C1 F G h k i) (@one_cat_arrow_family_comparison_from B C C1 F G h k i)) walking_arrow_src) (@id (Functor_cat B C) F) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k)) walking_arrow_src)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_to B C C1 F G h k i) (@one_cat_arrow_family_comparison_from B C C1 F G h k i))
      (@eq_sym (@Transf B C F F) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k)) walking_arrow_src) (@id (Functor_cat B C) F) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@transf_arrow_diagram_func B C F G k))))
    (@eq_trans (@Transf B C G G) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_to B C C1 F G h k i) (@one_cat_arrow_family_comparison_from B C C1 F G h k i)) walking_arrow_tgt) (@id (Functor_cat B C) G) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k)) walking_arrow_tgt)
      (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_to B C C1 F G h k i) (@one_cat_arrow_family_comparison_from B C C1 F G h k i))
      (@eq_sym (@Transf B C G G) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C F G k) (@transf_arrow_diagram_func B C F G k) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G k)) walking_arrow_tgt) (@id (Functor_cat B C) G) (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt) (@transf_arrow_diagram_func B C F G k))));

// Keep the actual forward/inverse transformations in the existing isomorphism package.
symbol one_cat_arrow_family_comparison_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k))
  : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k))
≔ Struct_sigma (@one_cat_arrow_family_comparison_to B C C1 F G h k i) (Struct_sigma (@one_cat_arrow_family_comparison_from B C C1 F G h k i)
    (Struct_sigma (@one_cat_arrow_family_comparison_left_law B C C1 F G h k i)
      (@one_cat_arrow_family_comparison_right_law B C C1 F G h k i)));
