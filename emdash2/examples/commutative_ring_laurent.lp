/*
  Reviewer for canonical Laurent coordinate transitions.

  The selected maps are constructed by the existing polynomial and
  localization universal properties. A common-overlap presentation uses
  literal maps into one target ring and retains whole identity paths, not
  componentwise transition equations.
*/

require open emdash.emdash3_2_commutative_algebra_laurent;

// The Unit-indexed variable is the selected one-variable coordinate.
assert [A : τ CommRing]
  (P : τ (@CommRingPolynomialAlgebra A Unit_grpd)) ⊢
  @comm_ring_one_variable_polynomial_coordinate A P
  ≡ @comm_ring_polynomial_variables A Unit_grpd P tt;

// The inverse selected from a unit carries canonical unit evidence.
assert [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x)) ⊢
  @comm_ring_unit_inverse_is_unit R x u
  : τ (@CommRingUnitEvidence R (@comm_ring_unit_inverse R x u));

// Polynomial universality exposes the intended coordinate equation.
assert [A : τ CommRing]
  (P Q : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (LQ : τ (@CommRingLaurentLocalization A Q)) ⊢
  @comm_ring_laurent_polynomial_coordinate_path A P Q LQ
  : τ (@=
      (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd Q)
          (@comm_ring_one_variable_polynomial_coordinate A Q) LQ))
      (@comm_ring_hom_apply
        (@comm_ring_polynomial_target A Unit_grpd P)
        (@comm_ring_localization_target
          (@comm_ring_polynomial_target A Unit_grpd Q)
          (@comm_ring_one_variable_polynomial_coordinate A Q) LQ)
        (@comm_ring_laurent_polynomial_map A P Q LQ)
        (@comm_ring_one_variable_polynomial_coordinate A P))
      (@comm_ring_laurent_inverse_valuation A Q LQ tt));

// Localization universality constructs both orientations of the Laurent map.
assert [A : τ CommRing]
  (P Q : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (LP : τ (@CommRingLaurentLocalization A P))
  (LQ : τ (@CommRingLaurentLocalization A Q)) ⊢
  @comm_ring_laurent_transition_map A P Q LP LQ
  : τ (@CommRingHom
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd P)
        (@comm_ring_one_variable_polynomial_coordinate A P) LP)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd Q)
        (@comm_ring_one_variable_polynomial_coordinate A Q) LQ));

assert [A : τ CommRing]
  (P Q : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (LP : τ (@CommRingLaurentLocalization A P))
  (LQ : τ (@CommRingLaurentLocalization A Q)) ⊢
  @comm_ring_laurent_transition_map A Q P LQ LP
  : τ (@CommRingHom
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd Q)
        (@comm_ring_one_variable_polynomial_coordinate A Q) LQ)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd P)
        (@comm_ring_one_variable_polynomial_coordinate A P) LP));

// Its factor agreement is a whole pointwise triangle over the source ring.
assert [A : τ CommRing]
  (P Q : τ (@CommRingPolynomialAlgebra A Unit_grpd))
  (LP : τ (@CommRingLaurentLocalization A P))
  (LQ : τ (@CommRingLaurentLocalization A Q)) ⊢
  @comm_ring_laurent_transition_agreement A P Q LP LQ
  : τ (@CommRingLocalizationAgreement
      (@comm_ring_polynomial_target A Unit_grpd P)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd P)
        (@comm_ring_one_variable_polynomial_coordinate A P) LP)
      (@comm_ring_localization_target
        (@comm_ring_polynomial_target A Unit_grpd Q)
        (@comm_ring_one_variable_polynomial_coordinate A Q) LQ)
      (@comm_ring_localization_map
        (@comm_ring_polynomial_target A Unit_grpd P)
        (@comm_ring_one_variable_polynomial_coordinate A P) LP)
      (@comm_ring_laurent_transition_map A P Q LP LQ)
      (@comm_ring_laurent_polynomial_map A P Q LQ));

// Literal chart presentations reconstruct the existing polynomial and
// localization packages at their declared endpoints.
assert [A R L : τ CommRing]
  [h : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation A R L h)) ⊢
  @comm_ring_polynomial_target A Unit_grpd
    (@comm_ring_one_variable_localization_polynomial A R L h P)
  ≡ R;

assert [A R L : τ CommRing]
  [h : τ (@CommRingHom R L)]
  (P : τ (@CommRingOneVariableLocalizationPresentation A R L h)) ⊢
  @comm_ring_localization_target
    R
    (@comm_ring_one_variable_localization_coordinate A R L h P)
    (@comm_ring_one_variable_localization_package A R L h P)
  ≡ L;

// Two literal localization maps into L produce a canonical overlap
// endomorphism in each direction.
assert [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (source : τ (@CommRingOneVariableLocalizationPresentation
      A R L source_map))
  (target : τ (@CommRingOneVariableLocalizationPresentation
      A T L target_map)) ⊢
  @comm_ring_laurent_common_overlap_transition
    A R T L source_map target_map source target
  : τ (@CommRingHom L L);

// A retained Laurent-overlap presentation gives whole identity evidence for
// both internally constructed directions.
assert [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (P : τ (@CommRingLaurentOverlapPresentation
      A R T L source_map target_map)) ⊢
  @comm_ring_laurent_overlap_forward_identity
    A R T L source_map target_map P
  : τ (@= (@CommRingHom L L)
      (@comm_ring_laurent_common_overlap_transition
        A R T L source_map target_map
        (@comm_ring_laurent_overlap_source
          A R T L source_map target_map P)
        (@comm_ring_laurent_overlap_target
          A R T L source_map target_map P))
      (@id CommRing_cat L));

assert [A R T L : τ CommRing]
  [source_map : τ (@CommRingHom R L)]
  [target_map : τ (@CommRingHom T L)]
  (P : τ (@CommRingLaurentOverlapPresentation
      A R T L source_map target_map)) ⊢
  @comm_ring_laurent_overlap_reverse_identity
    A R T L source_map target_map P
  : τ (@= (@CommRingHom L L)
      (@comm_ring_laurent_common_overlap_transition
        A T R L target_map source_map
        (@comm_ring_laurent_overlap_target
          A R T L source_map target_map P)
        (@comm_ring_laurent_overlap_source
          A R T L source_map target_map P))
      (@id CommRing_cat L));
