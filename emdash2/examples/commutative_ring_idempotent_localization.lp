/*
  Reviewer for localization at an idempotent through the fixed image eR.

  The model is parametric in e^2=e.  These checks exercise subtype sethood,
  inherited ring computation, the scaling structure map, selected factors,
  and the full localization universal property.  A closed nontrivial
  idempotent awaits the separately gated product-ring consumer.
*/

require open emdash.emdash3_2_commutative_algebra_localization_idempotent;

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_idempotent_image_carrier_is_set R e
  : τ (IsSetGrpd (@CommRingIdempotentImageCarrier R e));

assert (R : τ CommRing)
  (e x : τ (@comm_ring_carrier R))
  (fixed : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e x) x)) ⊢
  @comm_ring_idempotent_image_element
    R e (@comm_ring_idempotent_image_intro R e x fixed)
  ≡ x;

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image R e idempotent
  : τ CommRing;

// All five operations compute through the fixed-point subtype presentation.
assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_zero (@comm_ring_idempotent_image R e idempotent))
  ≡ @comm_ring_zero R;

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_one (@comm_ring_idempotent_image R e idempotent))
  ≡ e;

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x y : τ (@CommRingIdempotentImageCarrier R e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_add
      (@comm_ring_idempotent_image R e idempotent) x y)
  ≡ @comm_ring_add R
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y);

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x : τ (@CommRingIdempotentImageCarrier R e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_neg
      (@comm_ring_idempotent_image R e idempotent) x)
  ≡ @comm_ring_neg R
      (@comm_ring_idempotent_image_element R e x);

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x y : τ (@CommRingIdempotentImageCarrier R e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_mul
      (@comm_ring_idempotent_image R e idempotent) x y)
  ≡ @comm_ring_mul R
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y);

// The structure map computes to multiplication by e.
assert (R : τ CommRing)
  (e x : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image_element R e
    (@comm_ring_hom_apply
      R
      (@comm_ring_idempotent_image R e idempotent)
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      x)
  ≡ @comm_ring_mul R e x;

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image_localization_e_is_one R e idempotent
  : τ (@=
      (@comm_ring_carrier
        (@comm_ring_idempotent_image R e idempotent))
      (@comm_ring_hom_apply
        R
        (@comm_ring_idempotent_image R e idempotent)
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        e)
      (@comm_ring_one (@comm_ring_idempotent_image R e idempotent)));

// In any target, invertible idempotent h(e) is forced to be one.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e))) ⊢
  @comm_ring_hom_idempotent_unit_is_one R S h e idempotent unit
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h e)
      (@comm_ring_one S));

// The selected factor simply applies h to the retained underlying element.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  (x : τ (@CommRingIdempotentImageCarrier R e)) ⊢
  @comm_ring_hom_apply
    (@comm_ring_idempotent_image R e idempotent)
    S
    (@comm_ring_idempotent_image_factor_map
      R e idempotent S h unit)
    x
  ≡ @comm_ring_hom_apply R S h
      (@comm_ring_idempotent_image_element R e x);

assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e))) ⊢
  @comm_ring_idempotent_image_factor_is_contr
    R e idempotent S h unit
  : τ (IsContr (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h));

// The selected package exposes the fixed-image target and scaling map.
assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_idempotent_image_localization R e idempotent
  : τ (@CommRingLocalizationAt R e);

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_localization_target
    R e
    (@comm_ring_idempotent_image_localization R e idempotent)
  ≡ @comm_ring_idempotent_image R e idempotent;

assert (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)) ⊢
  @comm_ring_localization_map
    R e
    (@comm_ring_idempotent_image_localization R e idempotent)
  ≡ @comm_ring_idempotent_image_localization_map R e idempotent;
