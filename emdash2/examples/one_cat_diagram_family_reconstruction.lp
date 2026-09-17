/* The original arbitrary D and selected reconstruction maps are retained. */
require open emdash.emdash3_2_one_cat_diagram_family_reconstruction;
// catalog-area: Whole arrow-family categorical isomorphisms

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_diagram_family_reconstruction_to B C C1 D) walking_arrow_src
  ≡ @id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_diagram_family_reconstruction_to B C C1 D) walking_arrow_tgt
  ≡ @id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_diagram_family_reconstruction_from B C C1 D) walking_arrow_src
  ≡ @id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) ⊢
  @sym_transf_tapp0_transf B WalkingArrow_cat C _ _
    (@one_cat_diagram_family_reconstruction_from B C C1 D) walking_arrow_tgt
  ≡ @id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) ⊢
  @iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D
    (@one_cat_diagram_family_reconstruction_evidence B C C1 D) ≡ (@one_cat_diagram_family_reconstruction_to B C C1 D);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) ⊢
  @iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
      (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D
    (@one_cat_diagram_family_reconstruction_evidence B C C1 D) ≡ (@one_cat_diagram_family_reconstruction_from B C C1 D);
