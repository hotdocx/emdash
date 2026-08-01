/*
  Reviewer-facing PSSS-07d example: polynomial algebras by universal property.

  The executable model proves R[Empty] = R for every commutative ring. It
  selects no positive-variable polynomial representation or monomial syntax.
*/

require open emdash.emdash3_2_commutative_algebra_polynomial;

// Public agreement and factor boundaries.
assert (R P S : τ CommRing)
  (base_map : τ (@CommRingHom R P))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S)) ⊢
  @CommRingPolynomialBaseAgreement R P S base_map factor h
  : Grpd;

assert (R P S : τ CommRing)
  (base_map : τ (@CommRingHom R P))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_polynomial_base_agreement_is_prop
    R P S base_map factor h
  : τ (IsPropGrpd
      (@CommRingPolynomialBaseAgreement R P S base_map factor h));

assert (X : Grpd)
  (P S : τ CommRing)
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @CommRingPolynomialVariableAgreement X P S variables factor valuation
  : Grpd;

assert (X : Grpd)
  (P S : τ CommRing)
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @comm_ring_polynomial_variable_agreement_is_prop
    X P S variables factor valuation
  : τ (IsPropGrpd
      (@CommRingPolynomialVariableAgreement
        X P S variables factor valuation));

assert (R P S : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @comm_ring_polynomial_factor_agreement_is_prop
    R P S X base_map variables factor h valuation
  : τ (IsPropGrpd (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation));

assert (R P S : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S))) ⊢
  @CommRingPolynomialFactor R P S X base_map variables h valuation
  : Grpd;

assert (R P : τ CommRing)
  (X : Grpd)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P))) ⊢
  @IsCommRingPolynomialAlgebra R X P base_map variables
  : Grpd;

assert (R : τ CommRing)
  (X : Grpd) ⊢
  @CommRingPolynomialAlgebra R X
  : Grpd;

// Empty variable map for the generic equation R[Empty] = R.
symbol empty_polynomial_variables
  (R : τ CommRing)
  : τ (@Function_grpd Empty_grpd (@comm_ring_carrier R))
≔ λ x : τ Empty_grpd,
    @empty_elim
      (λ _ : τ Empty_grpd, @comm_ring_carrier R)
      x;

// The stable identity selected by this consumer computes only through its
// dedicated pointwise head.
assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R R (@comm_ring_hom_id_pointwise R) x
  ≡ x;

assert (R : τ CommRing) ⊢
  @comm_ring_hom_id_pointwise_path R
  : τ (@= (@CommRingHom R R)
      (@comm_ring_hom_id R)
      (@comm_ring_hom_id_pointwise R));

// For any target base map h, h itself is the centre extension.
symbol empty_polynomial_center_base
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingPolynomialBaseAgreement
      R R S (@comm_ring_hom_id_pointwise R) h h)
≔ λ x : τ (@comm_ring_carrier R),
    @eq_refl
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h x);

symbol empty_polynomial_center_variables
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S)))
  : τ (@CommRingPolynomialVariableAgreement
      Empty_grpd R S
      (@empty_polynomial_variables R)
      h valuation)
≔ λ x : τ Empty_grpd,
    @empty_elim
      (λ variable : τ Empty_grpd,
        @= (@comm_ring_carrier S)
          (@comm_ring_hom_apply R S h
            ((@empty_polynomial_variables R) variable))
          (valuation variable))
      x;

symbol empty_polynomial_center_agreement
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S)))
  : τ (@CommRingPolynomialFactorAgreement
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h h valuation)
≔ @comm_ring_polynomial_factor_agreement_intro
    R R S Empty_grpd
    (@comm_ring_hom_id_pointwise R)
    (@empty_polynomial_variables R)
    h h valuation
    (@empty_polynomial_center_base R S h)
    (@empty_polynomial_center_variables R S h valuation);

symbol empty_polynomial_factor_center
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S)))
  : τ (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation)
≔ @comm_ring_polynomial_factor_intro
    R R S Empty_grpd
    (@comm_ring_hom_id_pointwise R)
    (@empty_polynomial_variables R)
    h valuation
    h
    (@empty_polynomial_center_agreement R S h valuation);

assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S))) ⊢
  @comm_ring_polynomial_factor_map
    R R S Empty_grpd
    (@comm_ring_hom_id_pointwise R)
    (@empty_polynomial_variables R)
    h valuation
    (@empty_polynomial_factor_center R S h valuation)
  ≡ h;

// A competitor's base triangle identifies its map pointwise with the centre.
symbol empty_polynomial_competitor_pointwise
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S))]
  (candidate : τ (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation))
  : τ (@CommRingHomPointwisePath
      R S h
      (@comm_ring_polynomial_factor_map
        R R S Empty_grpd
        (@comm_ring_hom_id_pointwise R)
        (@empty_polynomial_variables R)
        h valuation candidate))
≔ λ x : τ (@comm_ring_carrier R),
    @eq_sym
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S
        (@comm_ring_polynomial_factor_map
          R R S Empty_grpd
          (@comm_ring_hom_id_pointwise R)
          (@empty_polynomial_variables R)
          h valuation candidate)
        x)
      (@comm_ring_hom_apply R S h x)
      ((@comm_ring_polynomial_factor_base
          R R S Empty_grpd
          (@comm_ring_hom_id_pointwise R)
          (@empty_polynomial_variables R)
          h valuation candidate)
        x);

symbol empty_polynomial_factor_map_path
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S))]
  (candidate : τ (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation))
  : τ (h = @comm_ring_polynomial_factor_map
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation candidate)
≔ @comm_ring_hom_ext
    R S h
    (@comm_ring_polynomial_factor_map
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation candidate)
    (@empty_polynomial_competitor_pointwise R S h valuation candidate);

// The map path plus unique proposition-valued agreement transport gives the
// full dependent-Sigma equality from centre to competitor.
symbol empty_polynomial_factor_path
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S))]
  (candidate : τ (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation))
  : τ (@= (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation)
      (@empty_polynomial_factor_center R S h valuation)
      candidate)
≔ @Struct_sigma
    (@= (@CommRingHom R S)
      h
      (@comm_ring_polynomial_factor_map
        R R S Empty_grpd
        (@comm_ring_hom_id_pointwise R)
        (@empty_polynomial_variables R)
        h valuation candidate))
    (λ p : τ (@= (@CommRingHom R S)
        h
        (@comm_ring_polynomial_factor_map
          R R S Empty_grpd
          (@comm_ring_hom_id_pointwise R)
          (@empty_polynomial_variables R)
          h valuation candidate)),
      @PathOver
        (@CommRingHom R S)
        (λ factor : τ (@CommRingHom R S),
          @CommRingPolynomialFactorAgreement
            R R S Empty_grpd
            (@comm_ring_hom_id_pointwise R)
            (@empty_polynomial_variables R)
            factor h valuation)
        h
        (@comm_ring_polynomial_factor_map
          R R S Empty_grpd
          (@comm_ring_hom_id_pointwise R)
          (@empty_polynomial_variables R)
          h valuation candidate)
        p
        (@empty_polynomial_center_agreement R S h valuation)
        (@comm_ring_polynomial_factor_agreement
          R R S Empty_grpd
          (@comm_ring_hom_id_pointwise R)
          (@empty_polynomial_variables R)
          h valuation candidate))
    (@empty_polynomial_factor_map_path R S h valuation candidate)
    (@comm_ring_polynomial_factor_agreement_pathover
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation
      h
      (@comm_ring_polynomial_factor_map
        R R S Empty_grpd
        (@comm_ring_hom_id_pointwise R)
        (@empty_polynomial_variables R)
        h valuation candidate)
      (@empty_polynomial_center_agreement R S h valuation)
      (@comm_ring_polynomial_factor_agreement
        R R S Empty_grpd
        (@comm_ring_hom_id_pointwise R)
        (@empty_polynomial_variables R)
        h valuation candidate)
      (@empty_polynomial_factor_map_path R S h valuation candidate));

symbol empty_polynomial_factor_is_contr
  (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S)))
  : τ (IsContr (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation))
≔ @Struct_sigma
    (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation)
    (λ centre : τ (@CommRingPolynomialFactor
        R R S Empty_grpd
        (@comm_ring_hom_id_pointwise R)
        (@empty_polynomial_variables R)
        h valuation),
      @Pi_grpd
        (@CommRingPolynomialFactor
          R R S Empty_grpd
          (@comm_ring_hom_id_pointwise R)
          (@empty_polynomial_variables R)
          h valuation)
        (λ candidate : τ (@CommRingPolynomialFactor
            R R S Empty_grpd
            (@comm_ring_hom_id_pointwise R)
            (@empty_polynomial_variables R)
            h valuation),
          @= (@CommRingPolynomialFactor
            R R S Empty_grpd
            (@comm_ring_hom_id_pointwise R)
            (@empty_polynomial_variables R)
            h valuation)
            centre candidate))
    (@empty_polynomial_factor_center R S h valuation)
    (λ candidate : τ (@CommRingPolynomialFactor
        R R S Empty_grpd
        (@comm_ring_hom_id_pointwise R)
        (@empty_polynomial_variables R)
        h valuation),
      @empty_polynomial_factor_path R S h valuation candidate);

symbol empty_is_polynomial
  (R : τ CommRing)
  : τ (@IsCommRingPolynomialAlgebra
      R Empty_grpd R
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R))
≔ λ S : τ CommRing,
    λ h : τ (@CommRingHom R S),
      λ valuation : τ (@Function_grpd
          Empty_grpd (@comm_ring_carrier S)),
        @empty_polynomial_factor_is_contr R S h valuation;

symbol empty_polynomial
  (R : τ CommRing)
  : τ (@CommRingPolynomialAlgebra R Empty_grpd)
≔ @comm_ring_polynomial_intro
    R Empty_grpd
    R
    (@comm_ring_hom_id_pointwise R)
    (@empty_polynomial_variables R)
    (@empty_is_polynomial R);

// The package and its named observations compute on the explicit model.
assert (R : τ CommRing) ⊢
  @empty_polynomial R
  : τ (@CommRingPolynomialAlgebra R Empty_grpd);

assert (R : τ CommRing) ⊢
  @comm_ring_polynomial_target R Empty_grpd (@empty_polynomial R)
  ≡ R;

assert (R : τ CommRing) ⊢
  @comm_ring_polynomial_base_map R Empty_grpd (@empty_polynomial R)
  ≡ @comm_ring_hom_id_pointwise R;

assert (R : τ CommRing) ⊢
  @comm_ring_polynomial_variables R Empty_grpd (@empty_polynomial R)
  ≡ @empty_polynomial_variables R;

assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd
      Empty_grpd (@comm_ring_carrier S))) ⊢
  @comm_ring_polynomial_factorization_is_contr
    R Empty_grpd R
    (@comm_ring_hom_id_pointwise R)
    (@empty_polynomial_variables R)
    (@empty_is_polynomial R)
    S h valuation
  : τ (IsContr (@CommRingPolynomialFactor
      R R S Empty_grpd
      (@comm_ring_hom_id_pointwise R)
      (@empty_polynomial_variables R)
      h valuation));

// Runtime and package boundaries stay explicit.
assertnot (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R R (@comm_ring_hom_id R) x
  ≡ x;

assertnot (R : τ CommRing)
  (X : Grpd)
  (polynomial : τ (@CommRingPolynomialAlgebra R X)) ⊢
  polynomial
  ≡ @comm_ring_polynomial_intro
      R X
      (@comm_ring_polynomial_target R X polynomial)
      (@comm_ring_polynomial_base_map R X polynomial)
      (@comm_ring_polynomial_variables R X polynomial)
      (@comm_ring_polynomial_property R X polynomial);
