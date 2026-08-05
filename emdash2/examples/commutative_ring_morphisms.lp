/*
  Reviewer-facing PSSS-06b example: structured commutative-ring morphisms and
  the ordinary CommRing_cat facade, without a carrier functor.
*/

require open emdash.emdash3_2_commutative_algebra_category;

// The public classifiers expose their carrier-function boundary directly.
assert (R S : τ CommRing)
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))) ⊢
  @CommRingHomLaws R S f
  : Grpd;

assert (R S : τ CommRing) ⊢
  @CommRingHom R S
  : Grpd;

// Preservation evidence is a property, and structured maps form a set.
assert (R S : τ CommRing)
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))) ⊢
  @comm_ring_hom_laws_is_prop R S f
  : τ (IsPropGrpd (@CommRingHomLaws R S f));

assert (R S : τ CommRing) ⊢
  @comm_ring_hom_is_set R S
  : τ (IsSetGrpd (@CommRingHom R S));

// The category uses the existing ring and structured-map classifiers directly.
assert ⊢ Obj CommRing_cat ≡ CommRing;

assert (R S : τ CommRing) ⊢
  Hom_cat CommRing_cat R S
  ≡ Path_cat (@CommRingHom R S);

assert ⊢ comm_ring_cat_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) CommRing_cat);

// Concrete constructor consumer: the unique point map is a zero-ring map.
symbol example_zero_comm_ring_hom_laws
  : τ (@CommRingHomLaws
      zero_comm_ring
      zero_comm_ring
      (λ _ : τ Unit_grpd, tt))
≔ @comm_ring_hom_laws_intro
    zero_comm_ring
    zero_comm_ring
    (λ _ : τ Unit_grpd, tt)
    (@eq_refl Unit_grpd tt)
    (@eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd, @eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt);

symbol example_zero_comm_ring_hom
  : τ (@CommRingHom zero_comm_ring zero_comm_ring)
≔ @comm_ring_hom_intro
    zero_comm_ring
    zero_comm_ring
    (λ _ : τ Unit_grpd, tt)
    example_zero_comm_ring_hom_laws;

assert ⊢ @comm_ring_hom_function
    zero_comm_ring zero_comm_ring example_zero_comm_ring_hom tt
  ≡ tt;

assert ⊢ @comm_ring_hom_apply
    zero_comm_ring zero_comm_ring example_zero_comm_ring_hom tt
  ≡ tt;

// All five named projections expose the retained constructor fields.
assert ⊢ @comm_ring_hom_zero_law
    zero_comm_ring zero_comm_ring example_zero_comm_ring_hom
  ≡ @eq_refl Unit_grpd tt;

assert ⊢ @comm_ring_hom_one_law
    zero_comm_ring zero_comm_ring example_zero_comm_ring_hom
  ≡ @eq_refl Unit_grpd tt;

assert ⊢ @comm_ring_hom_add_law
    zero_comm_ring zero_comm_ring example_zero_comm_ring_hom
  : τ (@CommRingHomPreservesAdd
      zero_comm_ring
      zero_comm_ring
      (@comm_ring_hom_function
        zero_comm_ring zero_comm_ring example_zero_comm_ring_hom));

assert ⊢ @comm_ring_hom_neg_law
    zero_comm_ring zero_comm_ring example_zero_comm_ring_hom
  : τ (@CommRingHomPreservesNeg
      zero_comm_ring
      zero_comm_ring
      (@comm_ring_hom_function
        zero_comm_ring zero_comm_ring example_zero_comm_ring_hom));

assert ⊢ @comm_ring_hom_mul_law
    zero_comm_ring zero_comm_ring example_zero_comm_ring_hom
  : τ (@CommRingHomPreservesMul
      zero_comm_ring
      zero_comm_ring
      (@comm_ring_hom_function
        zero_comm_ring zero_comm_ring example_zero_comm_ring_hom));

// Whole-arrow category units retain the generic runtime owners.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_hom_comp R R S h (@comm_ring_hom_id R)
  ≡ h;

assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_hom_comp R S S (@comm_ring_hom_id S) h
  ≡ h;

// No package eta or false projected identity computation is installed.
assertnot (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  h
  ≡ @comm_ring_hom_intro
      R S
      (@comm_ring_hom_function R S h)
      (@comm_ring_hom_laws R S h);

assertnot (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R R (@comm_ring_hom_id R) x
  ≡ x;
