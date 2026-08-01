/*
  Polynomial algebras by universal property.

  A polynomial algebra over R on a variable classifier X is a commutative
  ring P with a base map and variable map such that every target base map and
  valuation has a contractible structured extension space. This one-way
  module selects no monomial, coefficient-family, quotient, positive-variable
  representation, inductive syntax, runtime rule, unification rule, or eta.
*/

require open emdash.emdash3_2_commutative_algebra_category;

// Pointwise agreement over the base ring.
symbol CommRingPolynomialBaseAgreement
  [R P S : τ CommRing]
  (base_map : τ (@CommRingHom R P))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S))
  : Grpd
≔ @Pi_grpd
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier S)
        (@comm_ring_hom_apply P S factor
          (@comm_ring_hom_apply R P base_map x))
        (@comm_ring_hom_apply R S h x));

symbol comm_ring_polynomial_base_agreement_is_prop
  [R P S : τ CommRing]
  (base_map : τ (@CommRingHom R P))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S))
  : τ (IsPropGrpd
      (@CommRingPolynomialBaseAgreement R P S base_map factor h))
≔ @is_prop_pi
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier S)
        (@comm_ring_hom_apply P S factor
          (@comm_ring_hom_apply R P base_map x))
        (@comm_ring_hom_apply R S h x))
    (λ x : τ (@comm_ring_carrier R),
      (@comm_ring_carrier_is_set S)
        (@comm_ring_hom_apply P S factor
          (@comm_ring_hom_apply R P base_map x))
        (@comm_ring_hom_apply R S h x));

// Pointwise agreement on the chosen variables.
symbol CommRingPolynomialVariableAgreement
  [X : Grpd]
  [P S : τ CommRing]
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  : Grpd
≔ @Pi_grpd X
    (λ variable : τ X,
      @= (@comm_ring_carrier S)
        (@comm_ring_hom_apply P S factor (variables variable))
        (valuation variable));

symbol comm_ring_polynomial_variable_agreement_is_prop
  [X : Grpd]
  [P S : τ CommRing]
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  : τ (IsPropGrpd
      (@CommRingPolynomialVariableAgreement
        X P S variables factor valuation))
≔ @is_prop_pi X
    (λ variable : τ X,
      @= (@comm_ring_carrier S)
        (@comm_ring_hom_apply P S factor (variables variable))
        (valuation variable))
    (λ variable : τ X,
      (@comm_ring_carrier_is_set S)
        (@comm_ring_hom_apply P S factor (variables variable))
        (valuation variable));

// The complete agreement is retained evidence, but is proposition-valued.
symbol CommRingPolynomialFactorAgreement
  [R P S : τ CommRing]
  [X : Grpd]
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  : Grpd
≔ `Σ_ base_agreement : τ (@CommRingPolynomialBaseAgreement
      R P S base_map factor h),
    @CommRingPolynomialVariableAgreement
      X P S variables factor valuation;

symbol comm_ring_polynomial_factor_agreement_intro
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [factor : τ (@CommRingHom P S)]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (base_agreement : τ (@CommRingPolynomialBaseAgreement
      R P S base_map factor h))
  (variable_agreement : τ (@CommRingPolynomialVariableAgreement
      X P S variables factor valuation))
  : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation)
≔ @Struct_sigma
    (@CommRingPolynomialBaseAgreement R P S base_map factor h)
    (λ _ : τ (@CommRingPolynomialBaseAgreement
        R P S base_map factor h),
      @CommRingPolynomialVariableAgreement
        X P S variables factor valuation)
    base_agreement
    variable_agreement;

symbol comm_ring_polynomial_factor_base_agreement
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [factor : τ (@CommRingHom P S)]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (agreement : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation))
  : τ (@CommRingPolynomialBaseAgreement R P S base_map factor h)
≔ sigma_Fst agreement;

symbol comm_ring_polynomial_factor_variable_agreement
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [factor : τ (@CommRingHom P S)]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (agreement : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation))
  : τ (@CommRingPolynomialVariableAgreement
      X P S variables factor valuation)
≔ sigma_Snd agreement;

symbol comm_ring_polynomial_factor_agreement_is_prop
  [R P S : τ CommRing]
  [X : Grpd]
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (factor : τ (@CommRingHom P S))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  : τ (IsPropGrpd (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation))
≔ @is_trunc_sigma
    trunc_minus_one
    (@CommRingPolynomialBaseAgreement R P S base_map factor h)
    (λ _ : τ (@CommRingPolynomialBaseAgreement
        R P S base_map factor h),
      @CommRingPolynomialVariableAgreement
        X P S variables factor valuation)
    (@comm_ring_polynomial_base_agreement_is_prop
      R P S base_map factor h)
    (λ _ : τ (@CommRingPolynomialBaseAgreement
        R P S base_map factor h),
      @comm_ring_polynomial_variable_agreement_is_prop
        X P S variables factor valuation);

// A factor is a structured map with both pointwise agreements.
symbol CommRingPolynomialFactor
  [R P S : τ CommRing]
  [X : Grpd]
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  : Grpd
≔ `Σ_ factor : τ (@CommRingHom P S),
    @CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation;

symbol comm_ring_polynomial_factor_intro
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (factor : τ (@CommRingHom P S))
  (agreement : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor h valuation))
  : τ (@CommRingPolynomialFactor
      R P S X base_map variables h valuation)
≔ @Struct_sigma
    (@CommRingHom P S)
    (λ k : τ (@CommRingHom P S),
      @CommRingPolynomialFactorAgreement
        R P S X base_map variables k h valuation)
    factor
    agreement;

symbol comm_ring_polynomial_factor_map
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (factor : τ (@CommRingPolynomialFactor
      R P S X base_map variables h valuation))
  : τ (@CommRingHom P S)
≔ sigma_Fst factor;

symbol comm_ring_polynomial_factor_agreement
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (factor : τ (@CommRingPolynomialFactor
      R P S X base_map variables h valuation))
  : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables
      (@comm_ring_polynomial_factor_map
        R P S X base_map variables h valuation factor)
      h valuation)
≔ sigma_Snd factor;

symbol comm_ring_polynomial_factor_base
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (factor : τ (@CommRingPolynomialFactor
      R P S X base_map variables h valuation))
  : τ (@CommRingPolynomialBaseAgreement
      R P S base_map
      (@comm_ring_polynomial_factor_map
        R P S X base_map variables h valuation factor)
      h)
≔ @comm_ring_polynomial_factor_base_agreement
    R P S X base_map variables
    (@comm_ring_polynomial_factor_map
      R P S X base_map variables h valuation factor)
    h valuation
    (@comm_ring_polynomial_factor_agreement
      R P S X base_map variables h valuation factor);

symbol comm_ring_polynomial_factor_variables
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  (factor : τ (@CommRingPolynomialFactor
      R P S X base_map variables h valuation))
  : τ (@CommRingPolynomialVariableAgreement
      X P S variables
      (@comm_ring_polynomial_factor_map
        R P S X base_map variables h valuation factor)
      valuation)
≔ @comm_ring_polynomial_factor_variable_agreement
    R P S X base_map variables
    (@comm_ring_polynomial_factor_map
      R P S X base_map variables h valuation factor)
    h valuation
    (@comm_ring_polynomial_factor_agreement
      R P S X base_map variables h valuation factor);

// Universal property: every base map and valuation has a contractible
// extension space.
symbol IsCommRingPolynomialAlgebra
  (R : τ CommRing)
  (X : Grpd)
  (P : τ CommRing)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  : Grpd
≔ @Pi_grpd CommRing
    (λ S : τ CommRing,
      @Pi_grpd (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @Pi_grpd
            (@Function_grpd X (@comm_ring_carrier S))
            (λ valuation : τ (@Function_grpd
                X (@comm_ring_carrier S)),
              IsContr (@CommRingPolynomialFactor
                R P S X base_map variables h valuation))));

symbol comm_ring_polynomial_factorization_is_contr
  [R : τ CommRing]
  [X : Grpd]
  [P : τ CommRing]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  (property : τ (@IsCommRingPolynomialAlgebra
      R X P base_map variables))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (valuation : τ (@Function_grpd X (@comm_ring_carrier S)))
  : τ (IsContr (@CommRingPolynomialFactor
      R P S X base_map variables h valuation))
≔ property S h valuation;

// Chosen package of target, base map, variables, and universal data.
symbol CommRingPolynomialAlgebra
  (R : τ CommRing)
  (X : Grpd)
  : Grpd
≔ `Σ_ P : τ CommRing,
   `Σ_ base_map : τ (@CommRingHom R P),
   `Σ_ variables : τ (@Function_grpd X (@comm_ring_carrier P)),
       @IsCommRingPolynomialAlgebra R X P base_map variables;

symbol comm_ring_polynomial_intro
  [R : τ CommRing]
  [X : Grpd]
  (P : τ CommRing)
  (base_map : τ (@CommRingHom R P))
  (variables : τ (@Function_grpd X (@comm_ring_carrier P)))
  (property : τ (@IsCommRingPolynomialAlgebra
      R X P base_map variables))
  : τ (@CommRingPolynomialAlgebra R X)
≔ @Struct_sigma
    CommRing
    (λ T : τ CommRing,
      `Σ_ iota : τ (@CommRingHom R T),
      `Σ_ vars : τ (@Function_grpd X (@comm_ring_carrier T)),
          @IsCommRingPolynomialAlgebra R X T iota vars)
    P
    (@Struct_sigma
      (@CommRingHom R P)
      (λ iota : τ (@CommRingHom R P),
        `Σ_ vars : τ (@Function_grpd X (@comm_ring_carrier P)),
            @IsCommRingPolynomialAlgebra R X P iota vars)
      base_map
      (@Struct_sigma
        (@Function_grpd X (@comm_ring_carrier P))
        (λ vars : τ (@Function_grpd X (@comm_ring_carrier P)),
          @IsCommRingPolynomialAlgebra R X P base_map vars)
        variables
        property));

symbol comm_ring_polynomial_target
  [R : τ CommRing]
  [X : Grpd]
  (polynomial : τ (@CommRingPolynomialAlgebra R X))
  : τ CommRing
≔ sigma_Fst polynomial;

symbol comm_ring_polynomial_base_map
  [R : τ CommRing]
  [X : Grpd]
  (polynomial : τ (@CommRingPolynomialAlgebra R X))
  : τ (@CommRingHom R
      (@comm_ring_polynomial_target R X polynomial))
≔ sigma_Fst (sigma_Snd polynomial);

symbol comm_ring_polynomial_variables
  [R : τ CommRing]
  [X : Grpd]
  (polynomial : τ (@CommRingPolynomialAlgebra R X))
  : τ (@Function_grpd X
      (@comm_ring_carrier
        (@comm_ring_polynomial_target R X polynomial)))
≔ sigma_Fst (sigma_Snd (sigma_Snd polynomial));

symbol comm_ring_polynomial_property
  [R : τ CommRing]
  [X : Grpd]
  (polynomial : τ (@CommRingPolynomialAlgebra R X))
  : τ (@IsCommRingPolynomialAlgebra
      R X
      (@comm_ring_polynomial_target R X polynomial)
      (@comm_ring_polynomial_base_map R X polynomial)
      (@comm_ring_polynomial_variables R X polynomial))
≔ sigma_Snd (sigma_Snd (sigma_Snd polynomial));

// Property-valued agreement fibres transport uniquely along a factor-map
// path. This is sufficient to assemble paths in the full factor Sigma.
symbol comm_ring_polynomial_factor_agreement_pathover
  [R P S : τ CommRing]
  [X : Grpd]
  [base_map : τ (@CommRingHom R P)]
  [variables : τ (@Function_grpd X (@comm_ring_carrier P))]
  [h : τ (@CommRingHom R S)]
  [valuation : τ (@Function_grpd X (@comm_ring_carrier S))]
  [factor0 factor1 : τ (@CommRingHom P S)]
  (agreement0 : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor0 h valuation))
  (agreement1 : τ (@CommRingPolynomialFactorAgreement
      R P S X base_map variables factor1 h valuation))
  (p : τ (factor0 = factor1))
  : τ (@PathOver
      (@CommRingHom P S)
      (λ factor : τ (@CommRingHom P S),
        @CommRingPolynomialFactorAgreement
          R P S X base_map variables factor h valuation)
      factor0 factor1 p agreement0 agreement1)
≔ @ind_eqr
    (@CommRingHom P S)
    factor1
    (λ factor : τ (@CommRingHom P S),
      λ q : τ (factor = factor1),
        @Pi_grpd
          (@CommRingPolynomialFactorAgreement
            R P S X base_map variables factor h valuation)
          (λ evidence : τ (@CommRingPolynomialFactorAgreement
              R P S X base_map variables factor h valuation),
            @PathOver
              (@CommRingHom P S)
              (λ k : τ (@CommRingHom P S),
                @CommRingPolynomialFactorAgreement
                  R P S X base_map variables k h valuation)
              factor factor1 q evidence agreement1))
    (λ evidence : τ (@CommRingPolynomialFactorAgreement
        R P S X base_map variables factor1 h valuation),
      @is_contr_center
        (@= (@CommRingPolynomialFactorAgreement
          R P S X base_map variables factor1 h valuation)
          evidence agreement1)
        ((@comm_ring_polynomial_factor_agreement_is_prop
            R P S X base_map variables factor1 h valuation)
          evidence agreement1))
    factor0
    p
    agreement0;
