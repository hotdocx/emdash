/*
  Reviewer for presented finite basic-open Zariski covers and base change.

  The final zero-ring term starts with literal maximal-sieve membership at a
  chosen localization arrow and returns literal membership after affine base
  change.  The result exercises localization factorization, Sigma transport,
  canonical restriction-arrow postcomposition, and ordinary-sieve pullback.
*/

require open emdash.emdash3_2_commutative_algebra_zariski;
require open emdash.examples.commutative_ring_localization;

// Dependent finite evidence computes on visible family constructors.
assert [A : Grpd]
  (P : τ A → Grpd)
  (n : τ Nat_grpd)
  (x : τ A)
  (xs : τ (@FiniteFamily A n)) ⊢
  @FiniteFamilyAll
    A P (succ n) (@finite_family_cons A n x xs)
  ≡ @Product_grpd (P x) (@FiniteFamilyAll A P n xs);

assert [A : Grpd]
  [P : τ A → Grpd]
  [n : τ Nat_grpd]
  [x : τ A]
  [xs : τ (@FiniteFamily A n)]
  (head : τ (P x))
  (tail : τ (@FiniteFamilyAll A P n xs)) ⊢
  @finite_family_all_head
    A P n (@finite_family_cons A n x xs)
    (@finite_family_all_cons A P n x xs head tail)
  ≡ head;

// A supplied localization family stays aligned with its generators.
assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  @comm_ring_localization_family_head
    R zero
    (@finite_family_singleton (@comm_ring_carrier R) f)
    (@comm_ring_localization_family_singleton R f localization)
  ≡ localization;

assert (R : τ CommRing)
  (localization : τ (@CommRingLocalizationAt R (@comm_ring_one R))) ⊢
  @comm_ring_zariski_cover_family_presentation
    R (@comm_ring_unit_zariski_cover_family R localization)
  ≡ @comm_ring_unit_zariski_cover R;

assert (R : τ CommRing)
  (localization : τ (@CommRingLocalizationAt R (@comm_ring_one R))) ⊢
  @comm_ring_zariski_cover_family_length
    R (@comm_ring_unit_zariski_cover_family R localization)
  ≡ succ zero;

// The chosen localization exposes its affine domain and structural map.
assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  @into_restr_domain
    (Op_cat CommRing_cat) R
    (@comm_ring_basic_open_arrow R f localization)
  ≡ @comm_ring_localization_target R f localization;

assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  @into_restr_arrow
    (Op_cat CommRing_cat) R
    (@comm_ring_basic_open_arrow R f localization)
  ≡ @comm_ring_localization_map R f localization;

// The selected pointwise composite has a concrete carrier-action normal form.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply
    R
    (@comm_ring_localization_target
      S
      (@comm_ring_hom_apply R S h f)
      target_localization)
    (@comm_ring_basic_open_base_change_composite
      R S h f target_localization)
    x
  ≡ @comm_ring_hom_apply
      S
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_localization_map
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_hom_apply R S h x);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f))) ⊢
  @comm_ring_basic_open_base_change_factor_map
    R S h f source_localization target_localization
  : τ (@CommRingHom
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f))) ⊢
  @comm_ring_basic_open_base_change_triangle
    R S h f source_localization target_localization
  : τ (@=
      (@CommRingHom
        R
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization))
      (@comm_ring_hom_comp
        R
        (@comm_ring_localization_target R f source_localization)
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_factor_map
          R S h f source_localization target_localization)
        (@comm_ring_localization_map R f source_localization))
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f))) ⊢
  @comm_ring_basic_open_base_change_into_arrow
    R S h f source_localization target_localization
  : τ (Hom
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@comm_ring_basic_open_arrow R f source_localization)
      (Struct_sigma
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization)));

// Pointwise composition does not runtime-collapse to the canonical slice image.
assertnot [R S T : τ CommRing]
  (h : τ (@CommRingHom R S))
  (g : τ (@CommRingHom S T)) ⊢
  @into_restr_postcompose
    (Op_cat CommRing_cat)
    S R h
    (Struct_sigma T g)
  ≡ @Struct_sigma
      (Obj CommRing_cat)
      (λ L : τ (Obj CommRing_cat),
        Obj (@Fibre_cat
          CommRing_cat
          (@yoneda_psh (Op_cat CommRing_cat) R)
          L))
      T
      (@comm_ring_hom_comp_pointwise R S T g h);

// Nevertheless the theorem-level comparison and final membership map exist.
assert [R S T : τ CommRing]
  (h : τ (@CommRingHom R S))
  (g : τ (@CommRingHom S T)) ⊢
  @comm_ring_affine_pointwise_postcomp_path R S T h g
  : τ (@=
      (@CommRingHom R T)
      (@comm_ring_hom_comp_pointwise R S T g h)
      (@hom_postcomp_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        T S R h g));

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@comm_ring_basic_open_arrow R f source_localization))) ⊢
  @comm_ring_basic_open_pullback_membership
    R S h f source_localization target_localization Q member
  : τ (@SieveMembership
      (Op_cat CommRing_cat)
      S
      (@sieve_pullback
        (Op_cat CommRing_cat)
        S R h Q)
      (@comm_ring_basic_open_arrow
        S
        (@comm_ring_hom_apply R S h f)
        target_localization));

// Closed nonempty consumer from the existing zero-ring localization model.
assert ⊢
  @comm_ring_unit_zariski_cover_family
    zero_comm_ring zero_localization_at_point
  : τ (@CommRingZariskiCoverFamily zero_comm_ring);

assert ⊢
  @comm_ring_basic_open_pullback_membership
    zero_comm_ring
    zero_comm_ring
    zero_localization_map
    tt
    zero_localization_at_point
    zero_localization_at_point
    (@maximal_sieve (Op_cat CommRing_cat) zero_comm_ring)
    tt
  : τ (@SieveMembership
      (Op_cat CommRing_cat)
      zero_comm_ring
      (@sieve_pullback
        (Op_cat CommRing_cat)
        zero_comm_ring
        zero_comm_ring
        zero_localization_map
        (@maximal_sieve (Op_cat CommRing_cat) zero_comm_ring))
      (@comm_ring_basic_open_arrow
        zero_comm_ring tt zero_localization_at_point));
