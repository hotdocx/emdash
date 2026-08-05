/*
  Reviewer for finite selected basic-open containment and bounded base change.

  The generic Nat recursion retains dependent evidence over independently
  selected source and target evidence families.  The Zariski specialization
  stores literal sieve-membership terms and maps the algebraic presentation
  while accepting all target localizations explicitly.  The closed zero-ring
  singleton exercises actual pulled-back membership without a topology,
  truncation, rigid membership facade, or Zariski-specific recursive rule.
*/

require open emdash.emdash3_2_commutative_algebra_zariski;
require open emdash.examples.commutative_ring_localization;

// Evidence over already-selected evidence computes by the Nat/Sigma owners.
assert [A : Grpd]
  (P : τ A → Grpd)
  (Q : Π x : τ A, τ (P x) → Grpd)
  (n : τ Nat_grpd)
  (x : τ A)
  (xs : τ (@FiniteFamily A n))
  (px : τ (P x))
  (evidence : τ (@FiniteFamilyAll A P n xs)) ⊢
  @FiniteFamilyAllOver
    A P Q
    (succ n)
    (@finite_family_cons A n x xs)
    (@finite_family_all_cons A P n x xs px evidence)
  ≡ @Product_grpd
      (Q x px)
      (@FiniteFamilyAllOver A P Q n xs evidence);

assert [A B : Grpd]
  (map : τ (@Function_grpd A B))
  [P : τ A → Grpd]
  [P2 : τ B → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  [Q2 : Π y : τ B, τ (P2 y) → Grpd]
  (step : Π x : τ A,
    Π px : τ (P x),
    Π py : τ (P2 (map x)),
      τ (Q x px) → τ (Q2 (map x) py))
  (n : τ Nat_grpd) ⊢
  @finite_family_all_over_map
    A B map P P2 Q Q2 step n
  : τ (@FiniteFamilyAllOverMap
      A B map P P2 Q Q2 n);

// A mapped cover retains the mapped presentation and supplied target choices.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (family : τ (@CommRingZariskiCoverFamily R))
  (target_localizations : τ (@CommRingLocalizationFamily
      S
      (@comm_ring_zariski_cover_family_length R family)
      (@finite_family_map
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)
        (@comm_ring_hom_function R S h)
        (@comm_ring_zariski_cover_family_length R family)
        (@comm_ring_zariski_cover_family_generators R family)))) ⊢
  @comm_ring_zariski_cover_family_presentation
    S
    (@comm_ring_zariski_cover_family_map
      R S h family target_localizations)
  ≡ @comm_ring_zariski_cover_map
      R S h (@comm_ring_zariski_cover_family_presentation R family);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (family : τ (@CommRingZariskiCoverFamily R))
  (target_localizations : τ (@CommRingLocalizationFamily
      S
      (@comm_ring_zariski_cover_family_length R family)
      (@finite_family_map
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)
        (@comm_ring_hom_function R S h)
        (@comm_ring_zariski_cover_family_length R family)
        (@comm_ring_zariski_cover_family_generators R family)))) ⊢
  @comm_ring_zariski_cover_family_localizations
    S
    (@comm_ring_zariski_cover_family_map
      R S h family target_localizations)
  ≡ target_localizations;

// The full selected-family containment wrapper is available independently.
assert [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R)) ⊢
  @CommRingZariskiCoverFamilyMembership R family Q
  : Grpd;

// Closed nonempty singleton: every returned member is an actual term.
assert ⊢
  @comm_ring_unit_basic_open_family_pullback_membership
    zero_comm_ring
    zero_comm_ring
    zero_localization_map
    zero_localization_at_point
    zero_localization_at_point
    (@maximal_sieve (Op_cat CommRing_cat) zero_comm_ring)
    tt
  : τ (@CommRingBasicOpenFamilyMembership
      zero_comm_ring
      (succ zero)
      (@finite_family_singleton Unit_grpd tt)
      (@comm_ring_localization_family_singleton
        zero_comm_ring tt zero_localization_at_point)
      (@sieve_pullback
        (Op_cat CommRing_cat)
        zero_comm_ring
        zero_comm_ring
        zero_localization_map
        (@maximal_sieve (Op_cat CommRing_cat) zero_comm_ring)));
