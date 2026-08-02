/*
  Identity localization at an already invertible element.

  If f is a unit of R, the pointwise identity map R -> R satisfies the full
  one-element localization universal property at f.  Every admissible map h
  factors through it by h itself; structured-map extensionality and the
  property-valued agreement fibre make that factorization space contractible.

  This is a universal-property-first construction.  It adds no fraction
  representation, rewrite rule, unification rule, chosen inverse operation,
  presheaf, topology, Spec, or scheme declaration.
*/

require open emdash.emdash3_2_commutative_algebra_localization;

// The multiplicative identity is canonically a unit, with itself as inverse.
symbol comm_ring_one_unit
  (R : τ CommRing)
  : τ (@CommRingUnitEvidence R (@comm_ring_one R))
≔ @comm_ring_unit_intro
    R
    (@comm_ring_one R)
    (@comm_ring_one R)
    ((@comm_ring_mul_one_law R) (@comm_ring_one R));

// Every map factors through the pointwise identity by reflexivity.
symbol comm_ring_unit_localization_center_agreement
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingLocalizationAgreement
      R R S (@comm_ring_hom_id_pointwise R) h h)
≔ λ x : τ (@comm_ring_carrier R),
    @eq_refl
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h x);

symbol comm_ring_unit_localization_factor_center
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h)
≔ @comm_ring_localization_factor_intro
    R R S (@comm_ring_hom_id_pointwise R) h
    h
    (@comm_ring_unit_localization_center_agreement R S h);

// A competing triangle identifies its map pointwise with the centre.
symbol comm_ring_unit_localization_competitor_pointwise
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  (candidate : τ (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h))
  : τ (@CommRingHomPointwisePath
      R S h
      (@comm_ring_localization_factor_map
        R R S (@comm_ring_hom_id_pointwise R) h candidate))
≔ λ x : τ (@comm_ring_carrier R),
    @eq_sym
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S
        (@comm_ring_localization_factor_map
          R R S (@comm_ring_hom_id_pointwise R) h candidate)
        x)
      (@comm_ring_hom_apply R S h x)
      ((@comm_ring_localization_factor_agreement
          R R S (@comm_ring_hom_id_pointwise R) h candidate)
        x);

symbol comm_ring_unit_localization_factor_map_path
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  (candidate : τ (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h))
  : τ (@=
      (@CommRingHom R S)
      h
      (@comm_ring_localization_factor_map
        R R S (@comm_ring_hom_id_pointwise R) h candidate))
≔ @comm_ring_hom_ext
    R S
    h
    (@comm_ring_localization_factor_map
      R R S (@comm_ring_hom_id_pointwise R) h candidate)
    (@comm_ring_unit_localization_competitor_pointwise R S h candidate);

// Map extensionality plus the property-valued agreement fibre gives Sigma equality.
symbol comm_ring_unit_localization_factor_path
  [R S : τ CommRing]
  [h : τ (@CommRingHom R S)]
  (candidate : τ (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h))
  : τ (@=
      (@CommRingLocalizationFactor
        R R S (@comm_ring_hom_id_pointwise R) h)
      (@comm_ring_unit_localization_factor_center R S h)
      candidate)
≔ @Struct_sigma
    (@= (@CommRingHom R S)
      h
      (@comm_ring_localization_factor_map
        R R S (@comm_ring_hom_id_pointwise R) h candidate))
    (λ p : τ (@= (@CommRingHom R S)
        h
        (@comm_ring_localization_factor_map
          R R S (@comm_ring_hom_id_pointwise R) h candidate)),
      @PathOver
        (@CommRingHom R S)
        (λ factor : τ (@CommRingHom R S),
          @CommRingLocalizationAgreement
            R R S (@comm_ring_hom_id_pointwise R) factor h)
        h
        (@comm_ring_localization_factor_map
          R R S (@comm_ring_hom_id_pointwise R) h candidate)
        p
        (@comm_ring_unit_localization_center_agreement R S h)
        (@comm_ring_localization_factor_agreement
          R R S (@comm_ring_hom_id_pointwise R) h candidate))
    (@comm_ring_unit_localization_factor_map_path R S h candidate)
    (@comm_ring_localization_agreement_pathover
      R R S
      (@comm_ring_hom_id_pointwise R)
      h
      h
      (@comm_ring_localization_factor_map
        R R S (@comm_ring_hom_id_pointwise R) h candidate)
      (@comm_ring_unit_localization_center_agreement R S h)
      (@comm_ring_localization_factor_agreement
        R R S (@comm_ring_hom_id_pointwise R) h candidate)
      (@comm_ring_unit_localization_factor_map_path R S h candidate));

// The full factorization space through the pointwise identity is contractible.
symbol comm_ring_unit_localization_factor_is_contr
  (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  : τ (IsContr (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h))
≔ @Struct_sigma
    (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h)
    (λ centre : τ (@CommRingLocalizationFactor
        R R S (@comm_ring_hom_id_pointwise R) h),
      @Pi_grpd
        (@CommRingLocalizationFactor
          R R S (@comm_ring_hom_id_pointwise R) h)
        (λ candidate : τ (@CommRingLocalizationFactor
            R R S (@comm_ring_hom_id_pointwise R) h),
          @= (@CommRingLocalizationFactor
            R R S (@comm_ring_hom_id_pointwise R) h)
            centre candidate))
    (@comm_ring_unit_localization_factor_center R S h)
    (λ candidate : τ (@CommRingLocalizationFactor
        R R S (@comm_ring_hom_id_pointwise R) h),
      @comm_ring_unit_localization_factor_path R S h candidate);

// If f is already a unit, id_R has the localization universal property at f.
symbol comm_ring_unit_is_identity_localization
  (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (unit : τ (@CommRingUnitEvidence R f))
  : τ (@IsCommRingLocalizationAt
      R f R (@comm_ring_hom_id_pointwise R))
≔ @comm_ring_localization_property_intro
    R f R (@comm_ring_hom_id_pointwise R)
    unit
    (λ S : τ CommRing,
      λ h : τ (@CommRingHom R S),
        λ _ : τ (@CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h f)),
          @comm_ring_unit_localization_factor_is_contr R S h);

// Selected identity-localization package for an already invertible element.
symbol comm_ring_unit_identity_localization
  (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (unit : τ (@CommRingUnitEvidence R f))
  : τ (@CommRingLocalizationAt R f)
≔ @comm_ring_localization_intro
    R f
    R
    (@comm_ring_hom_id_pointwise R)
    (@comm_ring_unit_is_identity_localization R f unit);

// Every ring therefore has a selected identity localization at one.
symbol comm_ring_identity_localization_at_one
  (R : τ CommRing)
  : τ (@CommRingLocalizationAt R (@comm_ring_one R))
≔ @comm_ring_unit_identity_localization
    R
    (@comm_ring_one R)
    (@comm_ring_one_unit R);
