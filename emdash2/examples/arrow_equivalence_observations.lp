/* Existing Ω evidence, observed without changing its arrow or choices. */
require open emdash.emdash3_2_arrow_equivalence_observations;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y)) ⊢
  @ArrowOmegaEvidence C (@lax_edge C x y f) ≡ @OmegaEquivAlong C x y f;
assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_arrow_observation C (@omega_arrow_data C x y f u) ≡ @lax_edge C x y f;
assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_arrow_observation_evidence C (@omega_arrow_data C x y f u) ≡ u;
assert [K C : Cat] (F G : τ (Functor K C)) (h : τ (@Transf K C F G))
  (u : τ (@OmegaEquivAlong (Functor_cat K C) F G h)) (x : τ (Obj K)) ⊢
  @omega_arrow_observation C (@omega_arrow_data_at K C (@omega_arrow_data (Functor_cat K C) F G h u) x)
  ≡ @lax_edge C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x h);
assert [K C : Cat] (F G : τ (Functor K C)) (h : τ (@Transf K C F G))
  (u : τ (@OmegaEquivAlong (Functor_cat K C) F G h)) (x : τ (Obj K)) ⊢
  @omega_arrow_observation_evidence C (@omega_arrow_data_at K C (@omega_arrow_data (Functor_cat K C) F G h u) x)
  ≡ @omega_equiv_along_fapp1_fapp0 (Functor_cat K C) C (@fapp0_func K C x) F G h u;
assert [C : Cat] (d : τ (OmegaArrowData C)) ⊢
  @omega_arrow_observation_evidence C d
  : τ (@ArrowOmegaEvidence C (@omega_arrow_observation C d));
