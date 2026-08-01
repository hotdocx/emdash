/*
  Universal-property comparison for one-element commutative-ring localizations.

  This rule-free downstream module compares localization first at f and then
  at the image of g with localization at f*g. It derives the two canonical
  maps and their pointwise structure-map triangles from contractible
  factorization. It selects no fractions, quotient syntax, package equality,
  or inverse law for the comparison maps.
*/

require open emdash.emdash3_2_commutative_algebra_localization;

// Move unit evidence in either direction along an element path.
symbol comm_ring_unit_transport_forward
  [R : τ CommRing]
  [x y : τ (@comm_ring_carrier R)]
  (p : τ (@= (@comm_ring_carrier R) x y))
  (u : τ (@CommRingUnitEvidence R x))
  : τ (@CommRingUnitEvidence R y)
≔ @ind_eq
    (@comm_ring_carrier R)
    y x
    (@eq_sym (@comm_ring_carrier R) x y p)
    (λ z : τ (@comm_ring_carrier R), @CommRingUnitEvidence R z)
    u;

symbol comm_ring_unit_transport_backward
  [R : τ CommRing]
  [x y : τ (@comm_ring_carrier R)]
  (p : τ (@= (@comm_ring_carrier R) x y))
  (u : τ (@CommRingUnitEvidence R y))
  : τ (@CommRingUnitEvidence R x)
≔ @ind_eq
    (@comm_ring_carrier R)
    x y p
    (λ z : τ (@comm_ring_carrier R), @CommRingUnitEvidence R z)
    u;

// Structured ring maps preserve explicit unit evidence.
symbol comm_ring_hom_preserves_unit
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [x : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x))
  : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h x))
≔ @comm_ring_unit_intro
    S
    (@comm_ring_hom_apply R S h x)
    (@comm_ring_hom_apply R S h
      (@comm_ring_unit_inverse R x u))
    (@eq_trans
      (@comm_ring_carrier S)
      (@comm_ring_mul S
        (@comm_ring_hom_apply R S h x)
        (@comm_ring_hom_apply R S h
          (@comm_ring_unit_inverse R x u)))
      (@comm_ring_hom_apply R S h
        (@comm_ring_mul R x (@comm_ring_unit_inverse R x u)))
      (@comm_ring_one S)
      (@eq_sym
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply R S h
          (@comm_ring_mul R x (@comm_ring_unit_inverse R x u)))
        (@comm_ring_mul S
          (@comm_ring_hom_apply R S h x)
          (@comm_ring_hom_apply R S h
            (@comm_ring_unit_inverse R x u)))
        ((@comm_ring_hom_mul_law R S h)
          x (@comm_ring_unit_inverse R x u)))
      (@eq_trans
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply R S h
          (@comm_ring_mul R x (@comm_ring_unit_inverse R x u)))
        (@comm_ring_hom_apply R S h (@comm_ring_one R))
        (@comm_ring_one S)
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (@comm_ring_hom_function R S h)
          (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
          (@comm_ring_one R)
          (@comm_ring_unit_law R x u))
        (@comm_ring_hom_one_law R S h)));

// The derived left-unit law is used by the product-of-units construction.
symbol comm_ring_one_mul_law
  [R : τ CommRing]
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_one R) x)
      x)
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R (@comm_ring_one R) x)
    (@comm_ring_mul R x (@comm_ring_one R))
    x
    ((@comm_ring_mul_comm_law R) (@comm_ring_one R) x)
    ((@comm_ring_mul_one_law R) x);

// A product of units is a unit, with the inverse factors in reverse order.
symbol comm_ring_unit_mul
  [R : τ CommRing]
  [x y : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x))
  (v : τ (@CommRingUnitEvidence R y))
  : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y))
≔ @comm_ring_unit_intro
    R
    (@comm_ring_mul R x y)
    (@comm_ring_mul R
      (@comm_ring_unit_inverse R y v)
      (@comm_ring_unit_inverse R x u))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_mul R x y)
        (@comm_ring_mul R
          (@comm_ring_unit_inverse R y v)
          (@comm_ring_unit_inverse R x u)))
      (@comm_ring_mul R x
        (@comm_ring_mul R y
          (@comm_ring_mul R
            (@comm_ring_unit_inverse R y v)
            (@comm_ring_unit_inverse R x u))))
      (@comm_ring_one R)
      ((@comm_ring_mul_assoc_law R)
        x y
        (@comm_ring_mul R
          (@comm_ring_unit_inverse R y v)
          (@comm_ring_unit_inverse R x u)))
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_mul R x
          (@comm_ring_mul R y
            (@comm_ring_mul R
              (@comm_ring_unit_inverse R y v)
              (@comm_ring_unit_inverse R x u))))
        (@comm_ring_mul R x
          (@comm_ring_mul R
            (@comm_ring_mul R y (@comm_ring_unit_inverse R y v))
            (@comm_ring_unit_inverse R x u)))
        (@comm_ring_one R)
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ z : τ (@comm_ring_carrier R),
            @comm_ring_mul R x z)
          (@comm_ring_mul R y
            (@comm_ring_mul R
              (@comm_ring_unit_inverse R y v)
              (@comm_ring_unit_inverse R x u)))
          (@comm_ring_mul R
            (@comm_ring_mul R y (@comm_ring_unit_inverse R y v))
            (@comm_ring_unit_inverse R x u))
          (@eq_sym
            (@comm_ring_carrier R)
            (@comm_ring_mul R
              (@comm_ring_mul R y (@comm_ring_unit_inverse R y v))
              (@comm_ring_unit_inverse R x u))
            (@comm_ring_mul R y
              (@comm_ring_mul R
                (@comm_ring_unit_inverse R y v)
                (@comm_ring_unit_inverse R x u)))
            ((@comm_ring_mul_assoc_law R)
              y
              (@comm_ring_unit_inverse R y v)
              (@comm_ring_unit_inverse R x u))))
        (@eq_trans
          (@comm_ring_carrier R)
          (@comm_ring_mul R x
            (@comm_ring_mul R
              (@comm_ring_mul R y (@comm_ring_unit_inverse R y v))
              (@comm_ring_unit_inverse R x u)))
          (@comm_ring_mul R x
            (@comm_ring_mul R
              (@comm_ring_one R)
              (@comm_ring_unit_inverse R x u)))
          (@comm_ring_one R)
          (@eq_ap
            (@comm_ring_carrier R)
            (@comm_ring_carrier R)
            (λ z : τ (@comm_ring_carrier R),
              @comm_ring_mul R x
                (@comm_ring_mul R z
                  (@comm_ring_unit_inverse R x u)))
            (@comm_ring_mul R y (@comm_ring_unit_inverse R y v))
            (@comm_ring_one R)
            (@comm_ring_unit_law R y v))
          (@eq_trans
            (@comm_ring_carrier R)
            (@comm_ring_mul R x
              (@comm_ring_mul R
                (@comm_ring_one R)
                (@comm_ring_unit_inverse R x u)))
            (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
            (@comm_ring_one R)
            (@eq_ap
              (@comm_ring_carrier R)
              (@comm_ring_carrier R)
              (λ z : τ (@comm_ring_carrier R),
                @comm_ring_mul R x z)
              (@comm_ring_mul R
                (@comm_ring_one R)
                (@comm_ring_unit_inverse R x u))
              (@comm_ring_unit_inverse R x u)
              (@comm_ring_one_mul_law
                R (@comm_ring_unit_inverse R x u)))
            (@comm_ring_unit_law R x u)))));

// If a product is a unit, then each factor is a unit.
symbol comm_ring_unit_mul_left
  [R : τ CommRing]
  [x y : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y)))
  : τ (@CommRingUnitEvidence R x)
≔ @comm_ring_unit_intro
    R x
    (@comm_ring_mul R y
      (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R x
        (@comm_ring_mul R y
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u)))
      (@comm_ring_mul R
        (@comm_ring_mul R x y)
        (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
      (@comm_ring_one R)
      (@eq_sym
        (@comm_ring_carrier R)
        (@comm_ring_mul R
          (@comm_ring_mul R x y)
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
        (@comm_ring_mul R x
          (@comm_ring_mul R y
            (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u)))
        ((@comm_ring_mul_assoc_law R)
          x y
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u)))
      (@comm_ring_unit_law R (@comm_ring_mul R x y) u));

symbol comm_ring_unit_mul_right
  [R : τ CommRing]
  [x y : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y)))
  : τ (@CommRingUnitEvidence R y)
≔ @comm_ring_unit_intro
    R y
    (@comm_ring_mul R x
      (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R y
        (@comm_ring_mul R x
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u)))
      (@comm_ring_mul R
        (@comm_ring_mul R y x)
        (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
      (@comm_ring_one R)
      (@eq_sym
        (@comm_ring_carrier R)
        (@comm_ring_mul R
          (@comm_ring_mul R y x)
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
        (@comm_ring_mul R y
          (@comm_ring_mul R x
            (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u)))
        ((@comm_ring_mul_assoc_law R)
          y x
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u)))
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_mul R
          (@comm_ring_mul R y x)
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
        (@comm_ring_mul R
          (@comm_ring_mul R x y)
          (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
        (@comm_ring_one R)
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ z : τ (@comm_ring_carrier R),
            @comm_ring_mul R z
              (@comm_ring_unit_inverse R (@comm_ring_mul R x y) u))
          (@comm_ring_mul R y x)
          (@comm_ring_mul R x y)
          ((@comm_ring_mul_comm_law R) y x))
        (@comm_ring_unit_law R (@comm_ring_mul R x y) u)));

// A two-stage localization first inverts f and then the image of g.
symbol CommRingIteratedLocalizationAt
  (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  : Grpd
≔ `Σ_ first : τ (@CommRingLocalizationAt R f),
    @CommRingLocalizationAt
      (@comm_ring_localization_target R f first)
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target R f first)
        (@comm_ring_localization_map R f first)
        g);

symbol comm_ring_iterated_localization_intro
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (first : τ (@CommRingLocalizationAt R f))
  (second : τ (@CommRingLocalizationAt
      (@comm_ring_localization_target R f first)
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target R f first)
        (@comm_ring_localization_map R f first)
        g)))
  : τ (@CommRingIteratedLocalizationAt R f g)
≔ @Struct_sigma
    (@CommRingLocalizationAt R f)
    (λ localization : τ (@CommRingLocalizationAt R f),
      @CommRingLocalizationAt
        (@comm_ring_localization_target R f localization)
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target R f localization)
          (@comm_ring_localization_map R f localization)
          g))
    first second;

symbol comm_ring_iterated_localization_first
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingLocalizationAt R f)
≔ sigma_Fst iterated;

symbol comm_ring_iterated_localization_intermediate
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ CommRing
≔ @comm_ring_localization_target R f
    (@comm_ring_iterated_localization_first R f g iterated);

symbol comm_ring_iterated_localization_first_map
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingHom R
      (@comm_ring_iterated_localization_intermediate
        R f g iterated))
≔ @comm_ring_localization_map R f
    (@comm_ring_iterated_localization_first R f g iterated);

symbol comm_ring_iterated_localization_second
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingLocalizationAt
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_first_map R f g iterated)
        g))
≔ sigma_Snd iterated;

symbol comm_ring_iterated_localization_target
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ CommRing
≔ @comm_ring_localization_target
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_hom_apply
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      g)
    (@comm_ring_iterated_localization_second R f g iterated);

symbol comm_ring_iterated_localization_second_map
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingHom
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated))
≔ @comm_ring_localization_map
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_hom_apply
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      g)
    (@comm_ring_iterated_localization_second R f g iterated);

// The selected stable composite is the structure map of the two-stage object.
symbol comm_ring_iterated_localization_map
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingHom R
      (@comm_ring_iterated_localization_target R f g iterated))
≔ @comm_ring_hom_comp_pointwise
    R
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_iterated_localization_first_map R f g iterated);

// The image of f stays a unit after the second localization map.
symbol comm_ring_iterated_localization_first_image_unit
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingUnitEvidence
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_second_map R f g iterated)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          f)))
≔ @comm_ring_hom_preserves_unit
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_hom_apply
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      f)
    (@comm_ring_localization_inverted_unit
      R f
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_localization_property R f
        (@comm_ring_iterated_localization_first R f g iterated)));

// The second localization directly makes the image of g a unit.
symbol comm_ring_iterated_localization_second_image_unit
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingUnitEvidence
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_second_map R f g iterated)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          g)))
≔ @comm_ring_localization_inverted_unit
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_hom_apply
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      g)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_localization_property
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_first_map R f g iterated)
        g)
      (@comm_ring_iterated_localization_second R f g iterated));

// Therefore the two-stage structure map sends f*g to a unit.
symbol comm_ring_iterated_localization_inverts_product
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  : τ (@CommRingUnitEvidence
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_map R f g iterated)
        (@comm_ring_mul R f g)))
≔ @comm_ring_unit_transport_backward
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_hom_apply
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_mul R f g))
    (@comm_ring_mul
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_map R f g iterated)
        f)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_map R f g iterated)
        g))
    ((@comm_ring_hom_mul_law
        R
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_map R f g iterated))
      f g)
    (@comm_ring_unit_mul
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_second_map R f g iterated)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          f))
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_second_map R f g iterated)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          g))
      (@comm_ring_iterated_localization_first_image_unit
        R f g iterated)
      (@comm_ring_iterated_localization_second_image_unit
        R f g iterated));

// A localization at f*g makes the product of the two point-images a unit.
symbol comm_ring_product_localization_image_unit
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingUnitEvidence
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_mul
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_localization_map
            R (@comm_ring_mul R f g) product_localization)
          f)
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_localization_map
            R (@comm_ring_mul R f g) product_localization)
          g)))
≔ @comm_ring_unit_transport_forward
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_hom_apply
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_mul R f g))
    (@comm_ring_mul
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        f)
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        g))
    ((@comm_ring_hom_mul_law
        R
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization))
      f g)
    (@comm_ring_localization_inverted_unit
      R
      (@comm_ring_mul R f g)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_property
        R (@comm_ring_mul R f g) product_localization));

symbol comm_ring_product_localization_left_unit
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingUnitEvidence
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        f))
≔ @comm_ring_unit_mul_left
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_hom_apply
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      f)
    (@comm_ring_hom_apply
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      g)
    (@comm_ring_product_localization_image_unit
      R f g product_localization);

symbol comm_ring_product_localization_right_unit
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingUnitEvidence
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        g))
≔ @comm_ring_unit_mul_right
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_hom_apply
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      f)
    (@comm_ring_hom_apply
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      g)
    (@comm_ring_product_localization_image_unit
      R f g product_localization);

// Universal property of R[1/(fg)] gives the forward comparison factor.
symbol comm_ring_iterated_localization_forward_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated))
≔ @is_contr_center
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated))
    (@comm_ring_localization_factorization_is_contr
      R
      (@comm_ring_mul R f g)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_property
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_iterated_localization_inverts_product
        R f g iterated));

// First reverse stage: factor R -> R[1/(fg)] through R -> R[1/f].
symbol comm_ring_iterated_localization_reverse_first_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ @is_contr_center
    (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
    (@comm_ring_localization_factorization_is_contr
      R f
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_localization_property R f
        (@comm_ring_iterated_localization_first R f g iterated))
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_product_localization_left_unit
        R f g product_localization));

symbol comm_ring_iterated_localization_reverse_first_map
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingHom
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization))
≔ @comm_ring_localization_factor_map
    R
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_first_map R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_reverse_first_factor
      R f g iterated product_localization);

// The first-stage agreement transports the unit image of g to its factor.
symbol comm_ring_iterated_localization_reverse_second_unit
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingUnitEvidence
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_reverse_first_map
          R f g iterated product_localization)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          g)))
≔ @comm_ring_unit_transport_backward
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_hom_apply
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_reverse_first_map
        R f g iterated product_localization)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_first_map R f g iterated)
        g))
    (@comm_ring_hom_apply
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      g)
    ((@comm_ring_localization_factor_agreement
        R
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_first_map R f g iterated)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_reverse_first_factor
          R f g iterated product_localization))
      g)
    (@comm_ring_product_localization_right_unit
      R f g product_localization);

// Second reverse stage: factor through localization at the image of g.
symbol comm_ring_iterated_localization_reverse_second_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingLocalizationFactor
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_iterated_localization_reverse_first_map
        R f g iterated product_localization))
≔ @is_contr_center
    (@CommRingLocalizationFactor
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_iterated_localization_reverse_first_map
        R f g iterated product_localization))
    (@comm_ring_localization_factorization_is_contr
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_first_map R f g iterated)
        g)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_localization_property
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          g)
        (@comm_ring_iterated_localization_second R f g iterated))
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_reverse_first_map
        R f g iterated product_localization)
      (@comm_ring_iterated_localization_reverse_second_unit
        R f g iterated product_localization));

symbol comm_ring_iterated_localization_reverse_map
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingHom
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization))
≔ @comm_ring_localization_factor_map
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_iterated_localization_reverse_first_map
      R f g iterated product_localization)
    (@comm_ring_iterated_localization_reverse_second_factor
      R f g iterated product_localization);

// The two staged triangles compose to a triangle over the original ring.
symbol comm_ring_iterated_localization_reverse_agreement
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingLocalizationAgreement
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_iterated_localization_reverse_map
        R f g iterated product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ λ x : τ (@comm_ring_carrier R),
    @eq_trans
      (@comm_ring_carrier
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_reverse_map
          R f g iterated product_localization)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_map R f g iterated)
          x))
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_reverse_first_map
          R f g iterated product_localization)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          x))
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        x)
      ((@comm_ring_localization_factor_agreement
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_second_map R f g iterated)
          (@comm_ring_iterated_localization_reverse_first_map
            R f g iterated product_localization)
          (@comm_ring_iterated_localization_reverse_second_factor
            R f g iterated product_localization))
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          x))
      ((@comm_ring_localization_factor_agreement
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          (@comm_ring_localization_map
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_reverse_first_factor
            R f g iterated product_localization))
        x);

symbol comm_ring_iterated_localization_reverse_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_reverse_map
      R f g iterated product_localization)
    (@comm_ring_iterated_localization_reverse_agreement
      R f g iterated product_localization);

// Comparison data consists of the canonical forward and staged reverse maps,
// each with its pointwise structure-map triangle. No inverse law is claimed.
symbol CommRingIteratedLocalizationComparison
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : Grpd
≔ @Product_grpd
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated))
    (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization));

symbol comm_ring_iterated_localization_comparison
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)
≔ @Product_pair_grpd
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated))
    (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
    (@comm_ring_iterated_localization_forward_factor
      R f g iterated product_localization)
    (@comm_ring_iterated_localization_reverse_factor
      R f g iterated product_localization);

// Named observations of an arbitrary comparison package.
symbol comm_ring_iterated_localization_comparison_forward_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated))
≔ sigma_Fst comparison;

symbol comm_ring_iterated_localization_comparison_reverse_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ sigma_Snd comparison;

symbol comm_ring_iterated_localization_comparison_forward_map
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated))
≔ @comm_ring_localization_factor_map
    R
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_factor
      R f g iterated product_localization comparison);

symbol comm_ring_iterated_localization_comparison_reverse_map
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingHom
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization))
≔ @comm_ring_localization_factor_map
    R
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_comparison_reverse_factor
      R f g iterated product_localization comparison);

symbol comm_ring_iterated_localization_comparison_forward_agreement
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationAgreement
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_map R f g iterated))
≔ @comm_ring_localization_factor_agreement
    R
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_factor
      R f g iterated product_localization comparison);

symbol comm_ring_iterated_localization_comparison_reverse_agreement
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationAgreement
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ @comm_ring_localization_factor_agreement
    R
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_comparison_reverse_factor
      R f g iterated product_localization comparison);
