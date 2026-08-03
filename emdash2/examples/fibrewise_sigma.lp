/*
  Reviewer for fibrewise dependent sums.

  Fibre computation and the whole first projection compute at their selected
  owners. The resulting family and displayed projection already carry base
  action and naturality internally; this first boundary adds no separate
  component equations or explicit base-arrow beta.
*/

require open emdash.emdash3_2_fibrewise_sigma;

// The composite family's value is the literal fibrewise dependent sum.
assert [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  (k : τ (Obj K)) ⊢
  @Fibre_cat K (@FibrewiseSigma_catd K E D) k
  ≡ @fibrewise_sigma_value_cat K E D k;

// The whole projection has the expected displayed-functor type.
assert [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E))) ⊢
  @fibrewise_sigma_proj1_funcd K E D
  : τ (Functord (@FibrewiseSigma_catd K E D) E);

// Its component is the ordinary first projection of the selected Sigma fibre.
assert [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  (k : τ (Obj K)) ⊢
  @tapp0_fapp0
    K Cat_cat
    (@FibrewiseSigma_catd K E D)
    E k
    (@fibrewise_sigma_proj1_funcd K E D)
  ≡ @Sigma_proj1_func
      (@Fibre_cat K E k)
      (@fibrewise_sigma_fibre_catd K E D k);

// A literal dependent pair projects to its retained first component.
assert [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  (k : τ (Obj K))
  (e : τ (Obj (@Fibre_cat K E k)))
  (d : τ (Obj (@Fibre_cat
      (@Fibre_cat K E k)
      (@fibrewise_sigma_fibre_catd K E D k)
      e))) ⊢
  @fapp0
    (@fibrewise_sigma_value_cat K E D k)
    (@Fibre_cat K E k)
    (@tapp0_fapp0
      K Cat_cat
      (@FibrewiseSigma_catd K E D)
      E k
      (@fibrewise_sigma_proj1_funcd K E D))
    (Struct_sigma e d)
  ≡ e;

// Base-arrow action exists as part of the whole family object.
assert [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  [k l : τ (Obj K)]
  (p : τ (Hom K k l)) ⊢
  @catd_transport_func
    K
    (@FibrewiseSigma_catd K E D)
    k l p
  : τ (Functor
      (@fibrewise_sigma_value_cat K E D k)
      (@fibrewise_sigma_value_cat K E D l));
