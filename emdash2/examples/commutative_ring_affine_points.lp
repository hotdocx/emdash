/*
  Reviewer-facing affine functor of points and represented basic opens.

  The affine Yoneda presheaf retains its whole generic object/arrow action.
  Its semantic invertibility sieve D(f) supplies the actual basic-open point
  predicate.  A selected localization represents that predicate on every
  test ring by a constructive TypeEquiv; no univalence or external naturality
  family is assumed.

  These assertions do not claim a whole natural equivalence of presheaves,
  a topology, sheafhood, or a general scheme.
*/

require open emdash.emdash3_2_commutative_algebra_affine_points;
require open emdash.emdash3_2_commutative_algebra_localization_split;

// catalog-area: Affine functor of points and represented basic opens
// Spec(R)(S) is the existing represented Hom category and point classifier.
assert (R : τ CommRing) ⊢
  @affine_spec_functor_of_points R
  : τ (@Psh (Op_cat CommRing_cat));

assert (R S : τ CommRing) ⊢
  @Fibre_cat
    CommRing_cat
    (@affine_spec_functor_of_points R)
    S
  ≡ Path_cat (@CommRingHom R S);

assert (R S : τ CommRing) ⊢
  @AffineSpecPoint R S
  ≡ @CommRingHom R S;

// The basic open is the existing ordinary semantic invertibility sieve.
assert [R : τ CommRing]
  (f : τ (@comm_ring_carrier R)) ⊢
  @affine_spec_basic_open_sieve R f
  : τ (@Sieve (Op_cat CommRing_cat) R);

// At S, a D(f)-point is exactly a ring map h:R->S with unit evidence for h(f).
assert [R : τ CommRing]
  (f : τ (@comm_ring_carrier R))
  (S : τ CommRing) ⊢
  @AffineSpecBasicOpenPoint R f S
  ≡ `Σ_ h : τ (@CommRingHom R S),
      @CommRingUnitEvidence S (@comm_ring_hom_apply R S h f);

assert [R S : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h f))) ⊢
  @affine_spec_basic_open_point_map
    R f S (@affine_spec_basic_open_point_intro R f S h unit)
  ≡ h;

assert [R S : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h f))) ⊢
  @affine_spec_basic_open_point_unit
    R f S (@affine_spec_basic_open_point_intro R f S h unit)
  ≡ unit;

// Restricting a localized point is whole pointwise ring-map composition.
assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S)) ⊢
  @affine_spec_basic_open_point_map
    R f S
    (@affine_spec_basic_open_point_from_localized_map
      R f localization S k)
  ≡ @comm_ring_hom_comp_pointwise
      R
      (@comm_ring_localization_target R f localization)
      S k
      (@comm_ring_localization_map R f localization);

// The selected inverse is a genuine localization factor with a whole-map
// triangle, not an object-only or externally natural operation.
assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S)) ⊢
  @affine_spec_basic_open_point_factor R f localization S p
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R f localization)
      S
      (@comm_ring_localization_map R f localization)
      (@affine_spec_basic_open_point_map R f S p));

assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S)) ⊢
  @affine_spec_basic_open_point_lift_triangle
    R f localization S p
  : τ (@=
      (@CommRingHom R S)
      (@comm_ring_hom_comp_pointwise
        R
        (@comm_ring_localization_target R f localization)
        S
        (@affine_spec_basic_open_point_lift
          R f localization S p)
        (@comm_ring_localization_map R f localization))
      (@affine_spec_basic_open_point_map R f S p));

// Both inverse laws are derived and assemble into a true type equivalence.
assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S)) ⊢
  @affine_spec_basic_open_point_left_law
    R f localization S k
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (@affine_spec_basic_open_point_lift
        R f localization S
        (@affine_spec_basic_open_point_from_localized_map
          R f localization S k))
      k);

assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S)) ⊢
  @affine_spec_basic_open_point_right_law
    R f localization S p
  : τ (@=
      (@AffineSpecBasicOpenPoint R f S)
      (@affine_spec_basic_open_point_from_localized_map
        R f localization S
        (@affine_spec_basic_open_point_lift
          R f localization S p))
      p);

assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  (S : τ CommRing) ⊢
  @affine_spec_basic_open_point_type_equiv
    R f localization S
  : τ (TypeEquiv
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (@AffineSpecBasicOpenPoint R f S));

assert [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S)) ⊢
  @type_equiv_to
    (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S)
    (@AffineSpecBasicOpenPoint R f S)
    (@affine_spec_basic_open_point_type_equiv
      R f localization S)
    k
  ≡ @affine_spec_basic_open_point_from_localized_map
      R f localization S k;

// Closed non-endpoint witness: the split idempotent localization in F2 x F2
// represents its semantic D(e)-point classifier at the same target ring.
assert ⊢
  @affine_spec_basic_open_point_type_equiv
    f2_split_comm_ring
    f2_split_idempotent
    f2_split_idempotent_localization
    (@comm_ring_localization_target
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_localization)
  : τ (TypeEquiv
      (@CommRingHom
        (@comm_ring_localization_target
          f2_split_comm_ring
          f2_split_idempotent
          f2_split_idempotent_localization)
        (@comm_ring_localization_target
          f2_split_comm_ring
          f2_split_idempotent
          f2_split_idempotent_localization))
      (@AffineSpecBasicOpenPoint
        f2_split_comm_ring
        f2_split_idempotent
        (@comm_ring_localization_target
          f2_split_comm_ring
          f2_split_idempotent
          f2_split_idempotent_localization)));
