/*
  Canonical Laurent coordinate transitions by universal properties.

  A polynomial algebra on one Unit-indexed variable and a selected
  localization at that variable determine A[t,1/t]. Polynomial universality
  first constructs A[t] -> A[u,1/u], sending t to the chosen inverse of u;
  localization universality then extends it to a whole structured map
  A[t,1/t] -> A[u,1/u]. Reversing the inputs gives the opposite transition.

  `CommRingOneVariableLocalizationPresentation` applies the same construction
  to a literal map R -> L. `CommRingLaurentOverlapPresentation` presents two
  such maps with the same literal target L and retains whole paths saying
  that both canonical coordinate changes are its identity. This lets a
  concrete global consumer supply its coordinate identification without a
  disconnected overlap isomorphism or componentwise compatibility square.

  The module is transparent and rule-free. It adds no polynomial syntax,
  fraction normalizer, chosen global localization, runtime fold, external
  naturality field, projective-space object, or scheme declaration.
*/

require open emdash.emdash3_2_commutative_algebra_polynomial;
require open emdash.emdash3_2_commutative_algebra_localization;
require open emdash.emdash3_2_nat_arithmetic;

// Distinguished coordinate of a polynomial algebra on one Unit variable.
symbol comm_ring_one_variable_polynomial_coordinate
  [A : τ CommRing]
  (P : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  : τ (@comm_ring_carrier
      (@comm_ring_polynomial_target A Unit_grpd P))
≔ @comm_ring_polynomial_variables A Unit_grpd P tt;

// Selected localization of a one-variable polynomial algebra at its
// distinguished coordinate.
symbol CommRingLaurentLocalization
  (A : τ CommRing)
  (P : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  : Grpd
≔ @CommRingLocalizationAt
    (@comm_ring_polynomial_target A Unit_grpd P)
    (@comm_ring_one_variable_polynomial_coordinate A P);

// The chosen inverse of a unit is itself a unit, with inverse the original.
symbol comm_ring_unit_inverse_is_unit
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x))
  : τ (@CommRingUnitEvidence R (@comm_ring_unit_inverse R x u))
≔ @comm_ring_unit_intro
    R
    (@comm_ring_unit_inverse R x u)
    x
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_unit_inverse R x u) x)
      (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
      (@comm_ring_one R)
      ((@comm_ring_mul_comm_law R)
        (@comm_ring_unit_inverse R x u) x)
      (@comm_ring_unit_law R x u));

// The target coordinate is a unit after localization.
symbol comm_ring_laurent_target_coordinate_unit
  [A : τ CommRing]
  (target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingUnitEvidence
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_hom_apply
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_localization_map
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_one_variable_polynomial_coordinate A target)))
≔ @comm_ring_localization_inverted_unit
    (@comm_ring_polynomial_target A Unit_grpd target)
    (@comm_ring_one_variable_polynomial_coordinate A target)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    (@comm_ring_localization_map
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    (@comm_ring_localization_property
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization);

// The valuation sends the source coordinate to the inverse target coordinate.
symbol comm_ring_laurent_inverse_valuation
  [A : τ CommRing]
  (target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@Function_grpd
      Unit_grpd
      (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)))
≔ λ _ : τ Unit_grpd,
    @comm_ring_unit_inverse
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_hom_apply
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_localization_map
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_one_variable_polynomial_coordinate A target))
      (@comm_ring_laurent_target_coordinate_unit
        A target target_localization);

// The base map A -> target[1/u].
symbol comm_ring_laurent_target_base_map
  [A : τ CommRing]
  (target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingHom A
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization))
≔ @comm_ring_hom_comp_pointwise
    A
    (@comm_ring_polynomial_target A Unit_grpd target)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    (@comm_ring_localization_map
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    (@comm_ring_polynomial_base_map A Unit_grpd target);

// Polynomial universality constructs A[t] -> A[u,1/u], t |-> u^-1.
symbol comm_ring_laurent_polynomial_factor
  [A : τ CommRing]
  (source target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingPolynomialFactor
      A
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      Unit_grpd
      (@comm_ring_polynomial_base_map A Unit_grpd source)
      (@comm_ring_polynomial_variables A Unit_grpd source)
      (@comm_ring_laurent_target_base_map A target target_localization)
      (@comm_ring_laurent_inverse_valuation A target target_localization))
≔ @is_contr_center
    (@CommRingPolynomialFactor
      A
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      Unit_grpd
      (@comm_ring_polynomial_base_map A Unit_grpd source)
      (@comm_ring_polynomial_variables A Unit_grpd source)
      (@comm_ring_laurent_target_base_map A target target_localization)
      (@comm_ring_laurent_inverse_valuation A target target_localization))
    (@comm_ring_polynomial_factorization_is_contr
      A Unit_grpd
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_polynomial_base_map A Unit_grpd source)
      (@comm_ring_polynomial_variables A Unit_grpd source)
      (@comm_ring_polynomial_property A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_laurent_target_base_map A target target_localization)
      (@comm_ring_laurent_inverse_valuation A target target_localization));

symbol comm_ring_laurent_polynomial_map
  [A : τ CommRing]
  (source target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingHom
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization))
≔ @comm_ring_polynomial_factor_map
    A
    (@comm_ring_polynomial_target A Unit_grpd source)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    Unit_grpd
    (@comm_ring_polynomial_base_map A Unit_grpd source)
    (@comm_ring_polynomial_variables A Unit_grpd source)
    (@comm_ring_laurent_target_base_map A target target_localization)
    (@comm_ring_laurent_inverse_valuation A target target_localization)
    (@comm_ring_laurent_polynomial_factor
      A source target target_localization);

// Readable polynomial-variable equation: t maps to u^{-1}.
symbol comm_ring_laurent_polynomial_coordinate_path
  [A : τ CommRing]
  (source target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@=
      (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization))
      (@comm_ring_hom_apply
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_laurent_polynomial_map
          A source target target_localization)
        (@comm_ring_one_variable_polynomial_coordinate A source))
      (@comm_ring_laurent_inverse_valuation
        A target target_localization tt))
≔ (@comm_ring_polynomial_factor_variables
    A
    (@comm_ring_polynomial_target A Unit_grpd source)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    Unit_grpd
    (@comm_ring_polynomial_base_map A Unit_grpd source)
    (@comm_ring_polynomial_variables A Unit_grpd source)
    (@comm_ring_laurent_target_base_map A target target_localization)
    (@comm_ring_laurent_inverse_valuation A target target_localization)
    (@comm_ring_laurent_polynomial_factor
      A source target target_localization)) tt;

// The source coordinate maps to the inverse target coordinate and hence to a
// unit, as required by localization universality.
symbol comm_ring_laurent_polynomial_source_coordinate_unit
  [A : τ CommRing]
  (source target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingUnitEvidence
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_hom_apply
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_laurent_polynomial_map
          A source target target_localization)
        (@comm_ring_one_variable_polynomial_coordinate A source)))
≔ @comm_ring_unit_transport_backward
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    (@comm_ring_hom_apply
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_laurent_polynomial_map
        A source target target_localization)
      (@comm_ring_one_variable_polynomial_coordinate A source))
    (@comm_ring_laurent_inverse_valuation A target target_localization tt)
    ((@comm_ring_polynomial_factor_variables
        A
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        Unit_grpd
        (@comm_ring_polynomial_base_map A Unit_grpd source)
        (@comm_ring_polynomial_variables A Unit_grpd source)
        (@comm_ring_laurent_target_base_map A target target_localization)
        (@comm_ring_laurent_inverse_valuation A target target_localization)
        (@comm_ring_laurent_polynomial_factor
          A source target target_localization)) tt)
    (@comm_ring_unit_inverse_is_unit
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_hom_apply
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_localization_map
          (@comm_ring_polynomial_target A Unit_grpd target)
          (@comm_ring_one_variable_polynomial_coordinate A target)
          target_localization)
        (@comm_ring_one_variable_polynomial_coordinate A target))
      (@comm_ring_laurent_target_coordinate_unit
        A target target_localization));

// Localization universality extends the polynomial map to
// A[t,1/t] -> A[u,1/u].
symbol comm_ring_laurent_transition_factor
  [A : τ CommRing]
  (source target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (source_localization : τ (@CommRingLaurentLocalization A source))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingLocalizationFactor
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_localization_map
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_laurent_polynomial_map
        A source target target_localization))
≔ @is_contr_center
    (@CommRingLocalizationFactor
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_localization_map
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_laurent_polynomial_map
        A source target target_localization))
    (@comm_ring_localization_factorization_is_contr
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_one_variable_polynomial_coordinate A source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_localization_map
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_localization_property
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_laurent_polynomial_map
        A source target target_localization)
      (@comm_ring_laurent_polynomial_source_coordinate_unit
        A source target target_localization));

symbol comm_ring_laurent_transition_map
  [A : τ CommRing]
  (source target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (source_localization : τ (@CommRingLaurentLocalization A source))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingHom
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization))
≔ @comm_ring_localization_factor_map
    (@comm_ring_polynomial_target A Unit_grpd source)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_one_variable_polynomial_coordinate A source)
      source_localization)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    (@comm_ring_localization_map
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_one_variable_polynomial_coordinate A source)
      source_localization)
    (@comm_ring_laurent_polynomial_map A source target target_localization)
    (@comm_ring_laurent_transition_factor
      A source target source_localization target_localization);

// One actual map R -> L presented simultaneously as a one-variable
// polynomial chart over A and localization at its selected coordinate.
symbol CommRingOneVariableLocalizationPresentation
  (A R L : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  : Grpd
≔ `Σ_ base_map : τ (@CommRingHom A R),
   `Σ_ coordinate : τ (@comm_ring_carrier R),
      @Product_grpd
        (@IsCommRingPolynomialAlgebra
          A Unit_grpd R base_map
          (λ _ : τ Unit_grpd, coordinate))
        (@IsCommRingLocalizationAt R coordinate L localization_map);

symbol comm_ring_one_variable_localization_intro
  [A R L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (base_map : τ (@CommRingHom A R))
  (coordinate : τ (@comm_ring_carrier R))
  (polynomial : τ (@IsCommRingPolynomialAlgebra
      A Unit_grpd R base_map
      (λ _ : τ Unit_grpd, coordinate)))
  (localization : τ (@IsCommRingLocalizationAt
      R coordinate L localization_map))
  : τ (@CommRingOneVariableLocalizationPresentation
      A R L localization_map)
≔ @Struct_sigma
    (@CommRingHom A R)
    (λ base0 : τ (@CommRingHom A R),
      `Σ_ coordinate0 : τ (@comm_ring_carrier R),
        @Product_grpd
          (@IsCommRingPolynomialAlgebra
            A Unit_grpd R base0
            (λ _ : τ Unit_grpd, coordinate0))
          (@IsCommRingLocalizationAt
            R coordinate0 L localization_map))
    base_map
    (@Struct_sigma
      (@comm_ring_carrier R)
      (λ coordinate0 : τ (@comm_ring_carrier R),
        @Product_grpd
          (@IsCommRingPolynomialAlgebra
            A Unit_grpd R base_map
            (λ _ : τ Unit_grpd, coordinate0))
          (@IsCommRingLocalizationAt
            R coordinate0 L localization_map))
      coordinate
      (@Product_pair_grpd
        (@IsCommRingPolynomialAlgebra
          A Unit_grpd R base_map
          (λ _ : τ Unit_grpd, coordinate))
        (@IsCommRingLocalizationAt R coordinate L localization_map)
        polynomial localization));

symbol comm_ring_one_variable_localization_base_map
  [A R L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation
      A R L localization_map))
  : τ (@CommRingHom A R)
≔ sigma_Fst P;

symbol comm_ring_one_variable_localization_coordinate
  [A R L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation
      A R L localization_map))
  : τ (@comm_ring_carrier R)
≔ sigma_Fst (sigma_Snd P);

symbol comm_ring_one_variable_localization_polynomial_property
  [A R L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation
      A R L localization_map))
  : τ (@IsCommRingPolynomialAlgebra
      A Unit_grpd R
      (sigma_Fst P)
      (λ _ : τ Unit_grpd, sigma_Fst (sigma_Snd P)))
≔ sigma_Fst (sigma_Snd (sigma_Snd P));

symbol comm_ring_one_variable_localization_property
  [A R L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation
      A R L localization_map))
  : τ (@IsCommRingLocalizationAt
      R (sigma_Fst (sigma_Snd P)) L localization_map)
≔ sigma_Snd (sigma_Snd (sigma_Snd P));

// Existing packages reconstructed at their literal selected endpoints.
symbol comm_ring_one_variable_localization_polynomial
  [A R L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation
      A R L localization_map))
  : τ (@CommRingPolynomialAlgebra A Unit_grpd)
≔ @comm_ring_polynomial_intro
    A Unit_grpd R
    (sigma_Fst P)
    (λ _ : τ Unit_grpd, sigma_Fst (sigma_Snd P))
    (sigma_Fst (sigma_Snd (sigma_Snd P)));

symbol comm_ring_one_variable_localization_package
  [A R L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation
      A R L localization_map))
  : τ (@CommRingLaurentLocalization A
      (@comm_ring_one_variable_localization_polynomial
        A R L localization_map P))
≔ @comm_ring_localization_intro
    R
    (sigma_Fst (sigma_Snd P))
    L localization_map
    (sigma_Snd (sigma_Snd (sigma_Snd P)));

// Canonical coordinate inversion map on the literal common overlap.
symbol comm_ring_laurent_common_overlap_transition
  [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (source : τ (@CommRingOneVariableLocalizationPresentation
      A R L source_map))
  (target : τ (@CommRingOneVariableLocalizationPresentation
      A T L target_map))
  : τ (@CommRingHom L L)
≔ @comm_ring_laurent_transition_map
    A
    (@comm_ring_one_variable_localization_polynomial
      A R L source_map source)
    (@comm_ring_one_variable_localization_polynomial
      A T L target_map target)
    (@comm_ring_one_variable_localization_package
      A R L source_map source)
    (@comm_ring_one_variable_localization_package
      A T L target_map target);

// A Laurent overlap says both canonical coordinate changes are the identity
// of the actual shared target. These are whole structured-map paths.
symbol CommRingLaurentOverlapPresentation
  (A R T L : τ CommRing)
  (source_map : τ (@CommRingHom R L))
  (target_map : τ (@CommRingHom T L))
  : Grpd
≔ `Σ_ source : τ (@CommRingOneVariableLocalizationPresentation
      A R L source_map),
   `Σ_ target : τ (@CommRingOneVariableLocalizationPresentation
      A T L target_map),
      @Product_grpd
        (@= (@CommRingHom L L)
          (@comm_ring_laurent_common_overlap_transition
            A R T L source_map target_map source target)
          (@id CommRing_cat L))
        (@= (@CommRingHom L L)
          (@comm_ring_laurent_common_overlap_transition
            A T R L target_map source_map target source)
          (@id CommRing_cat L));

symbol comm_ring_laurent_overlap_intro
  [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (source : τ (@CommRingOneVariableLocalizationPresentation
      A R L source_map))
  (target : τ (@CommRingOneVariableLocalizationPresentation
      A T L target_map))
  (forward : τ (@= (@CommRingHom L L)
      (@comm_ring_laurent_common_overlap_transition
        A R T L source_map target_map source target)
      (@id CommRing_cat L)))
  (reverse : τ (@= (@CommRingHom L L)
      (@comm_ring_laurent_common_overlap_transition
        A T R L target_map source_map target source)
      (@id CommRing_cat L)))
  : τ (@CommRingLaurentOverlapPresentation
      A R T L source_map target_map)
≔ @Struct_sigma
    (@CommRingOneVariableLocalizationPresentation A R L source_map)
    (λ source0 : τ (@CommRingOneVariableLocalizationPresentation
        A R L source_map),
      `Σ_ target0 : τ (@CommRingOneVariableLocalizationPresentation
          A T L target_map),
        @Product_grpd
          (@= (@CommRingHom L L)
            (@comm_ring_laurent_common_overlap_transition
              A R T L source_map target_map source0 target0)
            (@id CommRing_cat L))
          (@= (@CommRingHom L L)
            (@comm_ring_laurent_common_overlap_transition
              A T R L target_map source_map target0 source0)
            (@id CommRing_cat L)))
    source
    (@Struct_sigma
      (@CommRingOneVariableLocalizationPresentation A T L target_map)
      (λ target0 : τ (@CommRingOneVariableLocalizationPresentation
          A T L target_map),
        @Product_grpd
          (@= (@CommRingHom L L)
            (@comm_ring_laurent_common_overlap_transition
              A R T L source_map target_map source target0)
            (@id CommRing_cat L))
          (@= (@CommRingHom L L)
            (@comm_ring_laurent_common_overlap_transition
              A T R L target_map source_map target0 source)
            (@id CommRing_cat L)))
      target
      (@Product_pair_grpd
        (@= (@CommRingHom L L)
          (@comm_ring_laurent_common_overlap_transition
            A R T L source_map target_map source target)
          (@id CommRing_cat L))
        (@= (@CommRingHom L L)
          (@comm_ring_laurent_common_overlap_transition
            A T R L target_map source_map target source)
          (@id CommRing_cat L))
        forward reverse));

symbol comm_ring_laurent_overlap_source
  [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (P : τ (@CommRingLaurentOverlapPresentation
      A R T L source_map target_map))
  : τ (@CommRingOneVariableLocalizationPresentation
      A R L source_map)
≔ sigma_Fst P;

symbol comm_ring_laurent_overlap_target
  [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (P : τ (@CommRingLaurentOverlapPresentation
      A R T L source_map target_map))
  : τ (@CommRingOneVariableLocalizationPresentation
      A T L target_map)
≔ sigma_Fst (sigma_Snd P);

symbol comm_ring_laurent_overlap_forward_identity
  [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (P : τ (@CommRingLaurentOverlapPresentation
      A R T L source_map target_map))
  : τ (@= (@CommRingHom L L)
      (@comm_ring_laurent_common_overlap_transition
        A R T L source_map target_map
        (sigma_Fst P) (sigma_Fst (sigma_Snd P)))
      (@id CommRing_cat L))
≔ sigma_Fst (sigma_Snd (sigma_Snd P));

symbol comm_ring_laurent_overlap_reverse_identity
  [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (P : τ (@CommRingLaurentOverlapPresentation
      A R T L source_map target_map))
  : τ (@= (@CommRingHom L L)
      (@comm_ring_laurent_common_overlap_transition
        A T R L target_map source_map
        (sigma_Fst (sigma_Snd P)) (sigma_Fst P))
      (@id CommRing_cat L))
≔ sigma_Snd (sigma_Snd (sigma_Snd P));


// Readable whole factor triangle for the Laurent transition.
symbol comm_ring_laurent_transition_agreement
  [A : τ CommRing]
  (source target : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (source_localization : τ (@CommRingLaurentLocalization A source))
  (target_localization : τ (@CommRingLaurentLocalization A target))
  : τ (@CommRingLocalizationAgreement
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd target)
        (@comm_ring_one_variable_polynomial_coordinate A target)
        target_localization)
      (@comm_ring_localization_map
        (@comm_ring_polynomial_target A Unit_grpd source)
        (@comm_ring_one_variable_polynomial_coordinate A source)
        source_localization)
      (@comm_ring_laurent_transition_map
        A source target source_localization target_localization)
      (@comm_ring_laurent_polynomial_map
        A source target target_localization))
≔ @comm_ring_localization_factor_agreement
    (@comm_ring_polynomial_target A Unit_grpd source)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_one_variable_polynomial_coordinate A source)
      source_localization)
    (@comm_ring_localization_target
      (@comm_ring_polynomial_target A Unit_grpd target)
      (@comm_ring_one_variable_polynomial_coordinate A target)
      target_localization)
    (@comm_ring_localization_map
      (@comm_ring_polynomial_target A Unit_grpd source)
      (@comm_ring_one_variable_polynomial_coordinate A source)
      source_localization)
    (@comm_ring_laurent_polynomial_map A source target target_localization)
    (@comm_ring_laurent_transition_factor
      A source target source_localization target_localization);
