/*
  Computational intersections of affine basic opens.

  For f,g:R and a test ring S, the explicit intersection point classifier is
  a whole structured map h:R->S together with unit evidence for h(f) and h(g).
  The structured-map multiplication law and the constructive product-unit
  operations give the fibre equivalence

      UnitEvidence(h(f*g))
        ~= UnitEvidence(h(f)) x UnitEvidence(h(g)).

  Because both fibres are propositions, the equivalence evidence is built
  directly from contractible homotopy fibres.  The same-base Sigma owner then
  gives D(f*g)(S) ~= D(f)(S) intersect D(g)(S).

  A chosen localization at f*g represents the intersection through a
  transparent two-equivalence chain: the existing public D(f*g)
  representability theorem followed by the explicit-Sigma intersection
  theorem.  Its forward/inverse maps and both laws are exposed without
  normalizing an entire TypeEquiv package through the public sieve-membership
  alias, which is a measured elaboration boundary.

  This rule-free component theorem connects already-internal sieves,
  represented presheaves, and localization charts.  It adds no object-only
  replacement, external naturality, whole-presheaf equality, univalence,
  topology, sheafification, rewrite rule, or unification rule.
*/

require open emdash.emdash3_2_commutative_algebra_affine_points;
require open emdash.emdash3_2_commutative_algebra_localization_comparison;

// A proposition with a selected point is contractible.
protected symbol affine_spec_prop_center_is_contr
  [A : Grpd]
  (hA : τ (IsPropGrpd A))
  (a : τ A)
  : τ (IsContr A)
≔ @Struct_sigma
    A
    (λ centre : τ A,
      @Pi_grpd A (λ x : τ A, @= A centre x))
    a
    (λ x : τ A,
      @is_contr_center (@= A a x) (hA a x));

// Between propositions, a map with a reverse-direction function is an
// equivalence map; no chosen inverse law is additional data.
protected symbol affine_spec_prop_map_is_equiv
  [A B : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ A)
  (hA : τ (IsPropGrpd A))
  (hB : τ (IsPropGrpd B))
  : τ (@IsEquivMap A B f)
≔ λ b : τ B,
    @is_contr_sigma
      A
      (λ a : τ A, @= B (f a) b)
      (@affine_spec_prop_center_is_contr A hA (g b))
      (λ a : τ A, hB (f a) b);

// Paired unit evidence uses the transparent constant-family Sigma product.
symbol AffineSpecBasicOpenUnitPair
  [R : τ CommRing]
  (f g : τ (@comm_ring_carrier R))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  : Grpd
≔ `Σ_ _ : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h f)),
    @CommRingUnitEvidence S (@comm_ring_hom_apply R S h g);

// A test-ring point in D(f) intersect D(g).
symbol AffineSpecBasicOpenIntersectionPoint
  [R : τ CommRing]
  (f g : τ (@comm_ring_carrier R))
  (S : τ CommRing)
  : Grpd
≔ `Σ_ h : τ (@CommRingHom R S),
    @AffineSpecBasicOpenUnitPair R f g S h;

symbol affine_spec_basic_open_product_unit_to_pair
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (u : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
  : τ (@AffineSpecBasicOpenUnitPair R f g S h)
≔ @Struct_sigma
    (@CommRingUnitEvidence S (@comm_ring_hom_apply R S h f))
    (λ _ : τ (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h f)),
      @CommRingUnitEvidence S (@comm_ring_hom_apply R S h g))
    (@comm_ring_unit_mul_left
      S
      (@comm_ring_hom_apply R S h f)
      (@comm_ring_hom_apply R S h g)
      (@comm_ring_unit_transport_forward
        S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))
        (@comm_ring_mul S
          (@comm_ring_hom_apply R S h f)
          (@comm_ring_hom_apply R S h g))
        ((@comm_ring_hom_mul_law R S h) f g)
        u))
    (@comm_ring_unit_mul_right
      S
      (@comm_ring_hom_apply R S h f)
      (@comm_ring_hom_apply R S h g)
      (@comm_ring_unit_transport_forward
        S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))
        (@comm_ring_mul S
          (@comm_ring_hom_apply R S h f)
          (@comm_ring_hom_apply R S h g))
        ((@comm_ring_hom_mul_law R S h) f g)
        u));

symbol affine_spec_basic_open_product_unit_from_pair
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (u : τ (@AffineSpecBasicOpenUnitPair R f g S h))
  : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
≔ @comm_ring_unit_transport_backward
    S
    (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))
    (@comm_ring_mul S
      (@comm_ring_hom_apply R S h f)
      (@comm_ring_hom_apply R S h g))
    ((@comm_ring_hom_mul_law R S h) f g)
    (@comm_ring_unit_mul
      S
      (@comm_ring_hom_apply R S h f)
      (@comm_ring_hom_apply R S h g)
      (sigma_Fst u)
      (sigma_Snd u));

symbol affine_spec_basic_open_product_unit_pair_is_prop
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (IsPropGrpd (@AffineSpecBasicOpenUnitPair R f g S h))
≔ @is_trunc_sigma
    trunc_minus_one
    (@CommRingUnitEvidence S (@comm_ring_hom_apply R S h f))
    (λ _ : τ (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h f)),
      @CommRingUnitEvidence S (@comm_ring_hom_apply R S h g))
    (@comm_ring_unit_evidence_is_prop
      S (@comm_ring_hom_apply R S h f))
    (λ _ : τ (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h f)),
      @comm_ring_unit_evidence_is_prop
        S (@comm_ring_hom_apply R S h g));

// Fibre equivalence: h(f*g) is a unit iff h(f) and h(g) are units.
symbol affine_spec_basic_open_product_unit_type_equiv
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (TypeEquiv
      (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
      (@AffineSpecBasicOpenUnitPair R f g S h))
≔ @Struct_sigma
    (@Function_grpd
      (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
      (@AffineSpecBasicOpenUnitPair R f g S h))
    (λ forward : τ (@Function_grpd
        (@CommRingUnitEvidence S
          (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
        (@AffineSpecBasicOpenUnitPair R f g S h)),
      @IsEquivMap
        (@CommRingUnitEvidence S
          (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
        (@AffineSpecBasicOpenUnitPair R f g S h)
        forward)
    (λ u : τ (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))),
      @affine_spec_basic_open_product_unit_to_pair R f g S h u)
    (@affine_spec_prop_map_is_equiv
      (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
      (@AffineSpecBasicOpenUnitPair R f g S h)
      (λ u : τ (@CommRingUnitEvidence S
          (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))),
        @affine_spec_basic_open_product_unit_to_pair R f g S h u)
      (λ u : τ (@AffineSpecBasicOpenUnitPair R f g S h),
        @affine_spec_basic_open_product_unit_from_pair R f g S h u)
      (@comm_ring_unit_evidence_is_prop
        S (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
      (@affine_spec_basic_open_product_unit_pair_is_prop R f g S h));

// Explicit-Sigma pointwise equivalence D(f*g)(S) ~= D(f)(S) intersect D(g)(S).
symbol affine_spec_basic_open_product_point_type_equiv
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (S : τ CommRing)
  : τ (TypeEquiv
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @AffineSpecBasicOpenUnitPair R f g S h)))
≔ @sigma_type_equiv_same_base
    (@CommRingHom R S)
    (λ h : τ (@CommRingHom R S),
      @CommRingUnitEvidence S
        (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))
    (λ h : τ (@CommRingHom R S),
      @AffineSpecBasicOpenUnitPair R f g S h)
    (λ h : τ (@CommRingHom R S),
      @affine_spec_basic_open_product_unit_type_equiv R f g S h);

symbol AffineSpecBasicOpenIntersectionRepresentation
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (S : τ CommRing)
  : Grpd
≔ Product_grpd
    (TypeEquiv
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S))
    (TypeEquiv
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@AffineSpecBasicOpenIntersectionPoint R f g S));

symbol affine_spec_basic_open_intersection_representation
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (S : τ CommRing)
  : τ (@AffineSpecBasicOpenIntersectionRepresentation
      R f g localization S)
≔ @Product_pair_grpd
    (TypeEquiv
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S))
    (TypeEquiv
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@AffineSpecBasicOpenIntersectionPoint R f g S))
    (@affine_spec_basic_open_point_type_equiv
      R (@comm_ring_mul R f g) localization S)
    (@affine_spec_basic_open_product_point_type_equiv R f g S);


// The two selected forward maps compose on their decoded point carriers.
symbol affine_spec_basic_open_intersection_representation_to
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  [S : τ CommRing]
  (representation : τ (@AffineSpecBasicOpenIntersectionRepresentation
      R f g localization S))
  (k : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S))
  : τ (@AffineSpecBasicOpenIntersectionPoint R f g S)
≔ @type_equiv_to
    (@Σ_
      (@CommRingHom R S)
      (λ h : τ (@CommRingHom R S),
        @CommRingUnitEvidence S
          (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
    (@AffineSpecBasicOpenIntersectionPoint R f g S)
    (sigma_Snd representation)
    (@type_equiv_to
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
      (sigma_Fst representation)
      k);

// The two selected inverse maps compose in the opposite order.
symbol affine_spec_basic_open_intersection_representation_from
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  [S : τ CommRing]
  (representation : τ (@AffineSpecBasicOpenIntersectionRepresentation
      R f g localization S))
  (p : τ (@AffineSpecBasicOpenIntersectionPoint R f g S))
  : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S)
≔ @type_equiv_from
    (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S)
    (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
    (sigma_Fst representation)
    (@type_equiv_from
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@AffineSpecBasicOpenIntersectionPoint R f g S)
      (sigma_Snd representation)
      p);

// Component left law for the executable two-step representation chain.
symbol affine_spec_basic_open_intersection_representation_left
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  [S : τ CommRing]
  (representation : τ (@AffineSpecBasicOpenIntersectionRepresentation
      R f g localization S))
  (k : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S))
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (@affine_spec_basic_open_intersection_representation_from
        R f g localization S representation
        (@affine_spec_basic_open_intersection_representation_to
          R f g localization S representation k))
      k)
≔ @eq_trans
    (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) localization)
      S)
    (@affine_spec_basic_open_intersection_representation_from
      R f g localization S representation
      (@affine_spec_basic_open_intersection_representation_to
        R f g localization S representation k))
    (@type_equiv_from
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
      (sigma_Fst representation)
      (@type_equiv_to
        (@CommRingHom
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) localization)
          S)
        (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
        (sigma_Fst representation)
        k))
    k
    (@eq_ap
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (λ q : τ (@Σ_
          (@CommRingHom R S)
          (λ h : τ (@CommRingHom R S),
            @CommRingUnitEvidence S
              (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))),
        @type_equiv_from
          (@CommRingHom
            (@comm_ring_localization_target
              R (@comm_ring_mul R f g) localization)
            S)
          (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
          (sigma_Fst representation)
          q)
      _ _
      (@type_equiv_left
        (@Σ_
          (@CommRingHom R S)
          (λ h : τ (@CommRingHom R S),
            @CommRingUnitEvidence S
              (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
        (@AffineSpecBasicOpenIntersectionPoint R f g S)
        (sigma_Snd representation)
        (@type_equiv_to
          (@CommRingHom
            (@comm_ring_localization_target
              R (@comm_ring_mul R f g) localization)
            S)
          (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
          (sigma_Fst representation)
          k)))
    (@type_equiv_left
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) localization)
        S)
      (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
      (sigma_Fst representation)
      k);

// Component right law for the executable two-step representation chain.
symbol affine_spec_basic_open_intersection_representation_right
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  [S : τ CommRing]
  (representation : τ (@AffineSpecBasicOpenIntersectionRepresentation
      R f g localization S))
  (p : τ (@AffineSpecBasicOpenIntersectionPoint R f g S))
  : τ (@=
      (@AffineSpecBasicOpenIntersectionPoint R f g S)
      (@affine_spec_basic_open_intersection_representation_to
        R f g localization S representation
        (@affine_spec_basic_open_intersection_representation_from
          R f g localization S representation p))
      p)
≔ @eq_trans
    (@AffineSpecBasicOpenIntersectionPoint R f g S)
    (@affine_spec_basic_open_intersection_representation_to
      R f g localization S representation
      (@affine_spec_basic_open_intersection_representation_from
        R f g localization S representation p))
    (@type_equiv_to
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@AffineSpecBasicOpenIntersectionPoint R f g S)
      (sigma_Snd representation)
      (@type_equiv_from
        (@Σ_
          (@CommRingHom R S)
          (λ h : τ (@CommRingHom R S),
            @CommRingUnitEvidence S
              (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
        (@AffineSpecBasicOpenIntersectionPoint R f g S)
        (sigma_Snd representation)
        p))
    p
    (@eq_ap
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@AffineSpecBasicOpenIntersectionPoint R f g S)
      (λ q : τ (@Σ_
          (@CommRingHom R S)
          (λ h : τ (@CommRingHom R S),
            @CommRingUnitEvidence S
              (@comm_ring_hom_apply R S h (@comm_ring_mul R f g)))),
        @type_equiv_to
          (@Σ_
            (@CommRingHom R S)
            (λ h : τ (@CommRingHom R S),
              @CommRingUnitEvidence S
                (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
          (@AffineSpecBasicOpenIntersectionPoint R f g S)
          (sigma_Snd representation)
          q)
      _ _
      (@type_equiv_right
        (@CommRingHom
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) localization)
          S)
        (@AffineSpecBasicOpenPoint R (@comm_ring_mul R f g) S)
        (sigma_Fst representation)
        (@type_equiv_from
          (@Σ_
            (@CommRingHom R S)
            (λ h : τ (@CommRingHom R S),
              @CommRingUnitEvidence S
                (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
          (@AffineSpecBasicOpenIntersectionPoint R f g S)
          (sigma_Snd representation)
          p)))
    (@type_equiv_right
      (@Σ_
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_mul R f g))))
      (@AffineSpecBasicOpenIntersectionPoint R f g S)
      (sigma_Snd representation)
      p);
