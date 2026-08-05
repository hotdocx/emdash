/*
  Reviewer example: finite families and algebraic Zariski-cover presentations.

  A finite family is a Nat-indexed right-associated Sigma record. Finite sums
  and dot products compute on visible constructors, structured ring maps
  preserve them propositionally, and explicit coefficients exhibit the unit
  ideal. These are algebraic cover-presentation data, not yet a Spec, basic
  open, localization family, sieve coverage, or topology.
*/

require open emdash.emdash3_2_commutative_algebra_finite;

// Formation and visible constructor computation.
assert [A : Grpd] ⊢ @FiniteFamily A zero ≡ Unit_grpd;

assert [A : Grpd] (n : τ Nat_grpd) ⊢
  @FiniteFamily A (succ n)
  ≡ @Σ_ A (λ _ : τ A, @FiniteFamily A n);

assertnot [A : Grpd] (n : τ Nat_grpd) ⊢
  @FiniteFamily A (succ n)
  ≡ @Product_grpd A (@FiniteFamily A n);

assertnot [A : Grpd]
  (xs : τ (@FiniteFamily A zero)) ⊢
  xs ≡ @finite_family_nil A;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (n : τ Nat_grpd)
  (x : τ A)
  (xs : τ (@FiniteFamily A n)) ⊢
  @finite_family_map A B f (succ n)
    (@finite_family_cons A n x xs)
  ≡ @finite_family_cons B n (f x)
      (@finite_family_map A B f n xs);

assert (R : τ CommRing) ⊢
  @comm_ring_finite_sum R zero (@finite_family_nil (@comm_ring_carrier R))
  ≡ @comm_ring_zero R;

assert (R : τ CommRing)
  (n : τ Nat_grpd)
  (x : τ (@comm_ring_carrier R))
  (xs : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_finite_sum R (succ n)
    (@finite_family_cons (@comm_ring_carrier R) n x xs)
  ≡ @comm_ring_add R x (@comm_ring_finite_sum R n xs);

assert (R : τ CommRing)
  (n : τ Nat_grpd)
  (a f : τ (@comm_ring_carrier R))
  (as0 fs0 : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_finite_dot R (succ n)
    (@finite_family_cons (@comm_ring_carrier R) n a as0)
    (@finite_family_cons (@comm_ring_carrier R) n f fs0)
  ≡ @comm_ring_add R
      (@comm_ring_mul R a f)
      (@comm_ring_finite_dot R n as0 fs0);

assert (A : Grpd)
  (A_is_set : τ (IsSetGrpd A))
  (n : τ Nat_grpd) ⊢
  @finite_family_is_set A A_is_set n
  : τ (IsSetGrpd (@FiniteFamily A n));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_hom_finite_sum_path R S h n xs
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h
        (@comm_ring_finite_sum R n xs))
      (@comm_ring_finite_sum S n
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n xs)));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (n : τ Nat_grpd)
  (as0 fs0 : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_hom_finite_dot_path R S h n as0 fs0
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h
        (@comm_ring_finite_dot R n as0 fs0))
      (@comm_ring_finite_dot S n
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n as0)
        (@finite_family_map
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          n fs0)));

assert [R : τ CommRing]
  (n : τ Nat_grpd)
  (generators : τ (@FiniteFamily (@comm_ring_carrier R) n)) ⊢
  @comm_ring_unimodular_is_set R n generators
  : τ (IsSetGrpd (@CommRingUnimodularPresentation R n generators));

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_is_set R
  : τ (IsSetGrpd (@CommRingZariskiCoverPresentation R));

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_length R (@comm_ring_unit_zariski_cover R)
  ≡ succ zero;

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_generators R (@comm_ring_unit_zariski_cover R)
  ≡ @finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (cover : τ (@CommRingZariskiCoverPresentation R)) ⊢
  @comm_ring_zariski_cover_map R S h cover
  : τ (@CommRingZariskiCoverPresentation S);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (cover : τ (@CommRingZariskiCoverPresentation R)) ⊢
  @comm_ring_zariski_cover_length S
    (@comm_ring_zariski_cover_map R S h cover)
  ≡ @comm_ring_zariski_cover_length R cover;

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (cover : τ (@CommRingZariskiCoverPresentation R)) ⊢
  @comm_ring_zariski_cover_generators S
    (@comm_ring_zariski_cover_map R S h cover)
  ≡ @finite_family_map
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_hom_function R S h)
      (@comm_ring_zariski_cover_length R cover)
      (@comm_ring_zariski_cover_generators R cover);

// The generic singleton [1] is an actual nonempty cover presentation.
assert (R : τ CommRing) ⊢
  @comm_ring_unimodular_coefficients
    R
    (succ zero)
    (@finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R))
    (@comm_ring_unit_unimodular R)
  ≡ @finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R);

assert (R : τ CommRing) ⊢
  @comm_ring_unimodular_law
    R
    (succ zero)
    (@finite_family_singleton
      (@comm_ring_carrier R)
      (@comm_ring_one R))
    (@comm_ring_unit_unimodular R)
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_finite_dot
        R
        (succ zero)
        (@finite_family_singleton
          (@comm_ring_carrier R)
          (@comm_ring_one R))
        (@finite_family_singleton
          (@comm_ring_carrier R)
          (@comm_ring_one R)))
      (@comm_ring_one R));

assert (R : τ CommRing) ⊢
  @comm_ring_zariski_cover_unimodular
    R
    (@comm_ring_unit_zariski_cover R)
  : τ (@CommRingUnimodularPresentation
      R
      (succ zero)
      (@finite_family_singleton
        (@comm_ring_carrier R)
        (@comm_ring_one R)));

// The binary helper consumes the correct unit-ideal equation a*f+b*g=1.
assert [R : τ CommRing]
  (f g a b : τ (@comm_ring_carrier R))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R a f)
        (@comm_ring_mul R b g))
      (@comm_ring_one R))) ⊢
  @comm_ring_binary_zariski_cover R f g a b law
  : τ (@CommRingZariskiCoverPresentation R);
