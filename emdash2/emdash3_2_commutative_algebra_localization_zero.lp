/*
  Universal-property localization at zero in the zero ring.

  The candidate is deliberately representation-free.  It derives x*0=0
  from the retained commutative-ring laws, proves that a ring in which zero
  is a unit is contractible at the carrier level, and uses that fact to make
  the zero ring the universal localization R[1/0].

  This rule-free construction is the computational empty-basic-open case. It
  is not a fraction representation or a nondegenerate localization model and
  declares no presheaf, topology, Spec, overlap, or scheme interface.
*/

require open emdash.emdash3_2_commutative_algebra_localization_unit;

// If a+a=a in an additive group, then a=0.
protected symbol comm_ring_add_idempotent_reduction
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  : τ (@=
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_add R a a)
        (@comm_ring_neg R a))
      a)
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_add R
      (@comm_ring_add R a a)
      (@comm_ring_neg R a))
    (@comm_ring_add R
      a
      (@comm_ring_add R a (@comm_ring_neg R a)))
    a
    ((@comm_ring_add_assoc_law R) a a (@comm_ring_neg R a))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        a
        (@comm_ring_add R a (@comm_ring_neg R a)))
      (@comm_ring_add R a (@comm_ring_zero R))
      a
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_add R a z)
        (@comm_ring_add R a (@comm_ring_neg R a))
        (@comm_ring_zero R)
        ((@comm_ring_add_inv_law R) a))
      ((@comm_ring_add_zero_law R) a));

symbol comm_ring_add_idempotent_is_zero
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  (idempotent : τ (@=
      (@comm_ring_carrier R)
      (@comm_ring_add R a a)
      a))
  : τ (@= (@comm_ring_carrier R) a (@comm_ring_zero R))
≔ @eq_trans
    (@comm_ring_carrier R)
    a
    (@comm_ring_add R
      (@comm_ring_add R a a)
      (@comm_ring_neg R a))
    (@comm_ring_zero R)
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_add R a a)
        (@comm_ring_neg R a))
      a
      (@comm_ring_add_idempotent_reduction R a))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_add R a a)
        (@comm_ring_neg R a))
      (@comm_ring_add R a (@comm_ring_neg R a))
      (@comm_ring_zero R)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R),
          @comm_ring_add R z (@comm_ring_neg R a))
        (@comm_ring_add R a a)
        a
        idempotent)
      ((@comm_ring_add_inv_law R) a));

// The retained one-sided distributivity basis derives multiplication by zero.
symbol comm_ring_mul_zero_right
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x (@comm_ring_zero R))
      (@comm_ring_zero R))
≔ @comm_ring_add_idempotent_is_zero
    R
    (@comm_ring_mul R x (@comm_ring_zero R))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R x (@comm_ring_zero R))
        (@comm_ring_mul R x (@comm_ring_zero R)))
      (@comm_ring_mul R x
        (@comm_ring_add R (@comm_ring_zero R) (@comm_ring_zero R)))
      (@comm_ring_mul R x (@comm_ring_zero R))
      (@eq_sym
        (@comm_ring_carrier R)
        (@comm_ring_mul R x
          (@comm_ring_add R (@comm_ring_zero R) (@comm_ring_zero R)))
        (@comm_ring_add R
          (@comm_ring_mul R x (@comm_ring_zero R))
          (@comm_ring_mul R x (@comm_ring_zero R)))
        ((@comm_ring_left_distrib_law R)
          x (@comm_ring_zero R) (@comm_ring_zero R)))
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R x z)
        (@comm_ring_add R (@comm_ring_zero R) (@comm_ring_zero R))
        (@comm_ring_zero R)
        ((@comm_ring_add_zero_law R) (@comm_ring_zero R))));

symbol comm_ring_mul_zero_left
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_zero R) x)
      (@comm_ring_zero R))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R (@comm_ring_zero R) x)
    (@comm_ring_mul R x (@comm_ring_zero R))
    (@comm_ring_zero R)
    ((@comm_ring_mul_comm_law R) (@comm_ring_zero R) x)
    (@comm_ring_mul_zero_right R x);

symbol comm_ring_neg_zero
  (R : τ CommRing)
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_neg R (@comm_ring_zero R)))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_zero R)
    (@comm_ring_add R
      (@comm_ring_zero R)
      (@comm_ring_neg R (@comm_ring_zero R)))
    (@comm_ring_neg R (@comm_ring_zero R))
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_zero R)
        (@comm_ring_neg R (@comm_ring_zero R)))
      (@comm_ring_zero R)
      ((@comm_ring_add_inv_law R) (@comm_ring_zero R)))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_zero R)
        (@comm_ring_neg R (@comm_ring_zero R)))
      (@comm_ring_add R
        (@comm_ring_neg R (@comm_ring_zero R))
        (@comm_ring_zero R))
      (@comm_ring_neg R (@comm_ring_zero R))
      ((@comm_ring_add_comm_law R)
        (@comm_ring_zero R)
        (@comm_ring_neg R (@comm_ring_zero R)))
      ((@comm_ring_add_zero_law R)
        (@comm_ring_neg R (@comm_ring_zero R))));

// Invertibility of zero forces zero=one.
symbol comm_ring_zero_unit_zero_one
  (R : τ CommRing)
  (unit : τ (@CommRingUnitEvidence R (@comm_ring_zero R)))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_one R))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_zero R)
    (@comm_ring_mul R
      (@comm_ring_zero R)
      (@comm_ring_unit_inverse R (@comm_ring_zero R) unit))
    (@comm_ring_one R)
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_zero R)
        (@comm_ring_unit_inverse R (@comm_ring_zero R) unit))
      (@comm_ring_zero R)
      (@comm_ring_mul_zero_left
        R
        (@comm_ring_unit_inverse R (@comm_ring_zero R) unit)))
    (@comm_ring_unit_law R (@comm_ring_zero R) unit);

// If zero=one, every element is equal to zero.
symbol comm_ring_zero_one_contracts
  (R : τ CommRing)
  (zero_one : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_one R)))
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R) (@comm_ring_zero R) x)
≔ @eq_sym
    (@comm_ring_carrier R)
    x
    (@comm_ring_zero R)
    (@eq_trans
      (@comm_ring_carrier R)
      x
      (@comm_ring_mul R x (@comm_ring_one R))
      (@comm_ring_zero R)
      (@eq_sym
        (@comm_ring_carrier R)
        (@comm_ring_mul R x (@comm_ring_one R))
        x
        ((@comm_ring_mul_one_law R) x))
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_mul R x (@comm_ring_one R))
        (@comm_ring_mul R x (@comm_ring_zero R))
        (@comm_ring_zero R)
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R x z)
          (@comm_ring_one R)
          (@comm_ring_zero R)
          (@eq_sym
            (@comm_ring_carrier R)
            (@comm_ring_zero R)
            (@comm_ring_one R)
            zero_one))
        (@comm_ring_mul_zero_right R x)));

// The unique point map R -> 0 is a structured ring homomorphism.
symbol comm_ring_hom_to_zero_laws
  (R : τ CommRing)
  : τ (@CommRingHomLaws
      R zero_comm_ring
      (λ _ : τ (@comm_ring_carrier R), tt))
≔ @comm_ring_hom_laws_intro
    R zero_comm_ring
    (λ _ : τ (@comm_ring_carrier R), tt)
    (@eq_refl Unit_grpd tt)
    (@eq_refl Unit_grpd tt)
    (λ _ : τ (@comm_ring_carrier R),
      λ _ : τ (@comm_ring_carrier R),
        @eq_refl Unit_grpd tt)
    (λ _ : τ (@comm_ring_carrier R), @eq_refl Unit_grpd tt)
    (λ _ : τ (@comm_ring_carrier R),
      λ _ : τ (@comm_ring_carrier R),
        @eq_refl Unit_grpd tt);

symbol comm_ring_hom_to_zero
  (R : τ CommRing)
  : τ (@CommRingHom R zero_comm_ring)
≔ @comm_ring_hom_intro
    R zero_comm_ring
    (λ _ : τ (@comm_ring_carrier R), tt)
    (@comm_ring_hom_to_zero_laws R);

// A zero=one witness selects the unique structured map 0 -> S.
symbol comm_ring_hom_from_zero_laws
  (S : τ CommRing)
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  : τ (@CommRingHomLaws
      zero_comm_ring S
      (λ _ : τ Unit_grpd, @comm_ring_zero S))
≔ @comm_ring_hom_laws_intro
    zero_comm_ring S
    (λ _ : τ Unit_grpd, @comm_ring_zero S)
    (@eq_refl (@comm_ring_carrier S) (@comm_ring_zero S))
    zero_one
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
        @eq_sym
          (@comm_ring_carrier S)
          (@comm_ring_add S (@comm_ring_zero S) (@comm_ring_zero S))
          (@comm_ring_zero S)
          ((@comm_ring_add_zero_law S) (@comm_ring_zero S)))
    (λ _ : τ Unit_grpd, @comm_ring_neg_zero S)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
        @eq_sym
          (@comm_ring_carrier S)
          (@comm_ring_mul S (@comm_ring_zero S) (@comm_ring_zero S))
          (@comm_ring_zero S)
          (@comm_ring_mul_zero_left S (@comm_ring_zero S)));

symbol comm_ring_hom_from_zero
  (S : τ CommRing)
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  : τ (@CommRingHom zero_comm_ring S)
≔ @comm_ring_hom_intro
    zero_comm_ring S
    (λ _ : τ Unit_grpd, @comm_ring_zero S)
    (@comm_ring_hom_from_zero_laws S zero_one);

symbol comm_ring_zero_localization_center_agreement
  (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  : τ (@CommRingLocalizationAgreement
      R zero_comm_ring S
      (@comm_ring_hom_to_zero R)
      (@comm_ring_hom_from_zero S zero_one)
      h)
≔ λ x : τ (@comm_ring_carrier R),
    @comm_ring_zero_one_contracts
      S zero_one (@comm_ring_hom_apply R S h x);

symbol comm_ring_zero_localization_factor_center
  (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  : τ (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h)
≔ @comm_ring_localization_factor_intro
    R zero_comm_ring S (@comm_ring_hom_to_zero R) h
    (@comm_ring_hom_from_zero S zero_one)
    (@comm_ring_zero_localization_center_agreement R S h zero_one);

symbol comm_ring_zero_localization_competitor_pointwise
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  (candidate : τ (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h))
  : τ (@CommRingHomPointwisePath
      zero_comm_ring S
      (@comm_ring_hom_from_zero S zero_one)
      (@comm_ring_localization_factor_map
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate))
≔ λ x : τ Unit_grpd,
    @comm_ring_zero_one_contracts
      S
      zero_one
      (@comm_ring_hom_apply
        zero_comm_ring S
        (@comm_ring_localization_factor_map
          R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate)
        x);

symbol comm_ring_zero_localization_factor_map_path
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  (candidate : τ (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h))
  : τ (@=
      (@CommRingHom zero_comm_ring S)
      (@comm_ring_hom_from_zero S zero_one)
      (@comm_ring_localization_factor_map
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate))
≔ @comm_ring_hom_ext
    zero_comm_ring S
    (@comm_ring_hom_from_zero S zero_one)
    (@comm_ring_localization_factor_map
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate)
    (@comm_ring_zero_localization_competitor_pointwise
      R S h zero_one candidate);

symbol comm_ring_zero_localization_factor_path
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  (candidate : τ (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h))
  : τ (@=
      (@CommRingLocalizationFactor
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h)
      (@comm_ring_zero_localization_factor_center R S h zero_one)
      candidate)
≔ @Struct_sigma
    (@= (@CommRingHom zero_comm_ring S)
      (@comm_ring_hom_from_zero S zero_one)
      (@comm_ring_localization_factor_map
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate))
    (λ p : τ (@= (@CommRingHom zero_comm_ring S)
        (@comm_ring_hom_from_zero S zero_one)
        (@comm_ring_localization_factor_map
          R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate)),
      @PathOver
        (@CommRingHom zero_comm_ring S)
        (λ factor : τ (@CommRingHom zero_comm_ring S),
          @CommRingLocalizationAgreement
            R zero_comm_ring S (@comm_ring_hom_to_zero R) factor h)
        (@comm_ring_hom_from_zero S zero_one)
        (@comm_ring_localization_factor_map
          R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate)
        p
        (@comm_ring_zero_localization_center_agreement R S h zero_one)
        (@comm_ring_localization_factor_agreement
          R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate))
    (@comm_ring_zero_localization_factor_map_path
      R S h zero_one candidate)
    (@comm_ring_localization_agreement_pathover
      R zero_comm_ring S
      (@comm_ring_hom_to_zero R)
      h
      (@comm_ring_hom_from_zero S zero_one)
      (@comm_ring_localization_factor_map
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate)
      (@comm_ring_zero_localization_center_agreement R S h zero_one)
      (@comm_ring_localization_factor_agreement
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h candidate)
      (@comm_ring_zero_localization_factor_map_path
        R S h zero_one candidate));

symbol comm_ring_zero_localization_factor_is_contr
  (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  : τ (IsContr (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h))
≔ @Struct_sigma
    (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h)
    (λ centre : τ (@CommRingLocalizationFactor
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h),
      @Pi_grpd
        (@CommRingLocalizationFactor
          R zero_comm_ring S (@comm_ring_hom_to_zero R) h)
        (λ candidate : τ (@CommRingLocalizationFactor
            R zero_comm_ring S (@comm_ring_hom_to_zero R) h),
          @= (@CommRingLocalizationFactor
            R zero_comm_ring S (@comm_ring_hom_to_zero R) h)
            centre candidate))
    (@comm_ring_zero_localization_factor_center R S h zero_one)
    (λ candidate : τ (@CommRingLocalizationFactor
        R zero_comm_ring S (@comm_ring_hom_to_zero R) h),
      @comm_ring_zero_localization_factor_path
        R S h zero_one candidate);

symbol comm_ring_hom_inverting_zero_unit
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h (@comm_ring_zero R))))
  : τ (@CommRingUnitEvidence S (@comm_ring_zero S))
≔ @comm_ring_unit_transport_forward
    S
    (@comm_ring_hom_apply R S h (@comm_ring_zero R))
    (@comm_ring_zero S)
    (@comm_ring_hom_zero_law R S h)
    unit;

symbol comm_ring_hom_inverting_zero_zero_one
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h (@comm_ring_zero R))))
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S))
≔ @comm_ring_zero_unit_zero_one
    S
    (@comm_ring_hom_inverting_zero_unit R S h unit);

symbol comm_ring_zero_is_zero_localization
  (R : τ CommRing)
  : τ (@IsCommRingLocalizationAt
      R (@comm_ring_zero R)
      zero_comm_ring
      (@comm_ring_hom_to_zero R))
≔ @comm_ring_localization_property_intro
    R (@comm_ring_zero R) zero_comm_ring (@comm_ring_hom_to_zero R)
    (@comm_ring_one_unit zero_comm_ring)
    (λ S : τ CommRing,
      λ h : τ (@CommRingHom R S),
        λ unit : τ (@CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h (@comm_ring_zero R))),
          @comm_ring_zero_localization_factor_is_contr
            R S h
            (@comm_ring_hom_inverting_zero_zero_one R S h unit));

symbol comm_ring_zero_localization
  (R : τ CommRing)
  : τ (@CommRingLocalizationAt R (@comm_ring_zero R))
≔ @comm_ring_localization_intro
    R (@comm_ring_zero R)
    zero_comm_ring
    (@comm_ring_hom_to_zero R)
    (@comm_ring_zero_is_zero_localization R);
