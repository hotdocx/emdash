/* Whole fixed-endpoint diagram comparisons retain the selected inverse. */
require open emdash.emdash3_2_one_cat_arrow_family_isomorphisms;
// catalog-area: Whole arrow-family categorical isomorphisms

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k)) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_arrow_family_comparison_to B C C1 F G h k i) walking_arrow_src
  ≡ @id (Functor_cat B C) F;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k)) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_arrow_family_comparison_to B C C1 F G h k i) walking_arrow_tgt
  ≡ @id (Functor_cat B C) G;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k)) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_arrow_family_comparison_from B C C1 F G h k i) walking_arrow_src
  ≡ @id (Functor_cat B C) F;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k)) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_arrow_family_comparison_from B C C1 F G h k i) walking_arrow_tgt
  ≡ @id (Functor_cat B C) G;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k)) ⊢
  @iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_evidence B C C1 F G h k i) ≡ (@one_cat_arrow_family_comparison_to B C C1 F G h k i);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [F G : τ (Functor B C)] [h k : τ (@Transf B C F G)]
  (i : τ (IsoEvidence (Hom_cat (Functor_cat B C) F G) h k)) ⊢
  @iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C F G h) (@transf_arrow_diagram_func B C F G k) (@one_cat_arrow_family_comparison_evidence B C C1 F G h k i) ≡ (@one_cat_arrow_family_comparison_from B C C1 F G h k i);
