/*
  Reviewer-facing intersections of affine basic opens.

  At every test ring S, D(f*g) is equivalent to the explicit intersection of
  D(f) and D(g).  A selected localization at f*g represents that intersection
  through two composable TypeEquiv capabilities with executable forward and
  inverse maps and propositional round trips.

  The theorem is componentwise between already-internal sieve/presheaf
  endpoints.  These assertions claim no whole natural equivalence, external
  naturality, topology, sheafification, univalence, or general scheme record.
*/

require open emdash.emdash3_2_commutative_algebra_affine_intersections;
require open emdash.emdash3_2_commutative_algebra_affine_atlas;

// catalog-area: Represented intersections of affine basic opens
// Intersection membership is one map with paired unit evidence.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @AffineSpecBasicOpenUnitPair R f g S h
  ≡ `Σ_ _ : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h f)),
      @CommRingUnitEvidence S (@comm_ring_hom_apply R S h g);

assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (S : τ CommRing) ⊢
  @AffineSpecBasicOpenIntersectionPoint R f g S
  ≡ `Σ_ h : τ (@CommRingHom R S),
      @AffineSpecBasicOpenUnitPair R f g S h;

// Paired unit evidence remains proposition-valued.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S)) ⊢
  @affine_spec_basic_open_product_unit_pair_is_prop R f g S h
  : τ (IsPropGrpd (@AffineSpecBasicOpenUnitPair R f g S h));

// Unit evidence at h(f*g) is equivalent to paired evidence at h(f), h(g).
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S)) ⊢
  @affine_spec_basic_open_product_unit_type_equiv R f g S h
  : τ (TypeEquiv
      (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
      (@AffineSpecBasicOpenUnitPair R f g S h));

assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (u : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))) ⊢
  @type_equiv_to
    (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
    (@AffineSpecBasicOpenUnitPair R f g S h)
    (@affine_spec_basic_open_product_unit_type_equiv R f g S h)
    u
  ≡ @affine_spec_basic_open_product_unit_to_pair R f g S h u;

// Same-base Sigma lifting gives the pointwise basic-open intersection.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (S : τ CommRing) ⊢
  @affine_spec_basic_open_product_point_type_equiv R f g S
  : τ (TypeEquiv
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@AffineSpecBasicOpenIntersectionPoint R f g S));

// Localization representation is retained as two explicit, composable
// equivalences instead of forcing package normalization through sieve aliases.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (S : τ CommRing) ⊢
  @affine_spec_basic_open_intersection_representation
    R f g localization S
  : τ (@AffineSpecBasicOpenIntersectionRepresentation
      R f g localization S);

assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S)) ⊢
  @affine_spec_basic_open_intersection_representation_to
    R f g localization S
    (@affine_spec_basic_open_intersection_representation
      R f g localization S)
    k
  : τ (@AffineSpecBasicOpenIntersectionPoint R f g S);

assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenIntersectionPoint R f g S)) ⊢
  @affine_spec_basic_open_intersection_representation_from
    R f g localization S
    (@affine_spec_basic_open_intersection_representation
      R f g localization S)
    p
  : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S);

// Both composite laws are derived from the two component TypeEquiv laws.
assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S)) ⊢
  @affine_spec_basic_open_intersection_representation_left
    R f g localization S
    (@affine_spec_basic_open_intersection_representation
      R f g localization S)
    k
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (@affine_spec_basic_open_intersection_representation_from
        R f g localization S
        (@affine_spec_basic_open_intersection_representation
          R f g localization S)
        (@affine_spec_basic_open_intersection_representation_to
          R f g localization S
          (@affine_spec_basic_open_intersection_representation
            R f g localization S)
          k))
      k);

assert [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenIntersectionPoint R f g S)) ⊢
  @affine_spec_basic_open_intersection_representation_right
    R f g localization S
    (@affine_spec_basic_open_intersection_representation
      R f g localization S)
    p
  : τ (@=
      (@AffineSpecBasicOpenIntersectionPoint R f g S)
      (@affine_spec_basic_open_intersection_representation_to
        R f g localization S
        (@affine_spec_basic_open_intersection_representation
          R f g localization S)
        (@affine_spec_basic_open_intersection_representation_from
          R f g localization S
          (@affine_spec_basic_open_intersection_representation
            R f g localization S)
          p))
      p);

// Closed atlas consumer: in F2 x F2 the two complementary chart generators
// multiply definitionally to zero, so the selected zero localization
// represents their empty intersection.
assert ⊢
  @affine_spec_basic_open_intersection_representation
    f2_split_comm_ring
    f2_split_idempotent
    f2_split_cosplit_idempotent
    (@comm_ring_zero_localization f2_split_comm_ring)
    zero_comm_ring
  : τ (@AffineSpecBasicOpenIntersectionRepresentation
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_cosplit_idempotent
      (@comm_ring_zero_localization f2_split_comm_ring)
      zero_comm_ring);
