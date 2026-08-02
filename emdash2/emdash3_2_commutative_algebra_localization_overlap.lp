/*
  Whole internal overlap equivalence for one-element localizations.

  Contractibility of universal-property factorization first proves that the
  canonical product/iterated comparison maps cancel on the product
  localization. Two successive uniqueness arguments then propagate the
  opposite cancellation through localization at f and localization at the
  image of g. The result is a native `OmegaEquivAlong CommRing_cat` and its
  first-class `OmegaEquiv` facade.

  This rule-free downstream module introduces no fraction representation,
  chosen-localization equality, presheaf restriction, topology, `Spec`, or
  scheme. All functorial/category structure remains at existing generic
  owners; the new laws are equalities of whole structured ring maps.
*/

require open emdash.emdash3_2_commutative_algebra_localization_comparison;

// Any two inhabitants of a contractible localization-factor space have
// equal selected structured maps.
symbol comm_ring_localization_factor_maps_equal
  [R L S : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  [h : τ (@CommRingHom R S)]
  (contractible : τ (IsContr (@CommRingLocalizationFactor
      R L S localization_map h)))
  (factor0 factor1 : τ (@CommRingLocalizationFactor
      R L S localization_map h))
  : τ (@= (@CommRingHom L S)
      (@comm_ring_localization_factor_map
        R L S localization_map h factor0)
      (@comm_ring_localization_factor_map
        R L S localization_map h factor1))
≔ @eq_ap
    (@CommRingLocalizationFactor R L S localization_map h)
    (@CommRingHom L S)
    (λ factor : τ (@CommRingLocalizationFactor
        R L S localization_map h),
      @comm_ring_localization_factor_map
        R L S localization_map h factor)
    factor0 factor1
    (@eq_trans
      (@CommRingLocalizationFactor R L S localization_map h)
      factor0
      (@is_contr_center
        (@CommRingLocalizationFactor R L S localization_map h)
        contractible)
      factor1
      (@eq_sym
        (@CommRingLocalizationFactor R L S localization_map h)
        (@is_contr_center
          (@CommRingLocalizationFactor R L S localization_map h)
          contractible)
        factor0
        (@is_contr_path
          (@CommRingLocalizationFactor R L S localization_map h)
          contractible factor0))
      (@is_contr_path
        (@CommRingLocalizationFactor R L S localization_map h)
        contractible factor1));

// The composite reverse∘forward agrees with the product-localization map.
protected symbol comm_ring_iterated_localization_comparison_left_agreement
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
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison))
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ λ x : τ (@comm_ring_carrier R),
    @eq_trans
      (@comm_ring_carrier
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_hom_comp_pointwise
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_comparison_reverse_map
            R f g iterated product_localization comparison)
          (@comm_ring_iterated_localization_comparison_forward_map
            R f g iterated product_localization comparison))
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_localization_map
            R (@comm_ring_mul R f g) product_localization)
          x))
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison)
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_map R f g iterated)
          x))
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        x)
      (@eq_ap
        (@comm_ring_carrier
          (@comm_ring_iterated_localization_target R f g iterated))
        (@comm_ring_carrier
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization))
        (λ y : τ (@comm_ring_carrier
            (@comm_ring_iterated_localization_target R f g iterated)),
          @comm_ring_hom_apply
            (@comm_ring_iterated_localization_target R f g iterated)
            (@comm_ring_localization_target
              R (@comm_ring_mul R f g) product_localization)
            (@comm_ring_iterated_localization_comparison_reverse_map
              R f g iterated product_localization comparison)
            y)
        (@comm_ring_hom_apply
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_comparison_forward_map
            R f g iterated product_localization comparison)
          (@comm_ring_hom_apply
            R
            (@comm_ring_localization_target
              R (@comm_ring_mul R f g) product_localization)
            (@comm_ring_localization_map
              R (@comm_ring_mul R f g) product_localization)
            x))
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_map R f g iterated)
          x)
        ((@comm_ring_iterated_localization_comparison_forward_agreement
            R f g iterated product_localization comparison)
          x))
      ((@comm_ring_iterated_localization_comparison_reverse_agreement
          R f g iterated product_localization comparison)
        x);

protected symbol comm_ring_iterated_localization_comparison_left_composite_factor
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
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison))
    (@comm_ring_iterated_localization_comparison_left_agreement
      R f g iterated product_localization comparison);

protected symbol comm_ring_iterated_localization_comparison_left_identity_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization))
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_hom_id_pointwise
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization))
    (λ x : τ (@comm_ring_carrier R),
      @eq_refl
        (@comm_ring_carrier
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization))
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_localization_map
            R (@comm_ring_mul R f g) product_localization)
          x));

protected symbol comm_ring_iterated_localization_comparison_left_law_pointwise
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id_pointwise
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)))
≔ @comm_ring_localization_factor_maps_equal
    R
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_map
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_localization_factorization_is_contr
      R
      (@comm_ring_mul R f g)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_property
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_inverted_unit
        R
        (@comm_ring_mul R f g)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_map
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_property
          R (@comm_ring_mul R f g) product_localization)))
    (@comm_ring_iterated_localization_comparison_left_composite_factor
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_left_identity_factor
      R f g product_localization);

// The stable pointwise cancellation transports explicitly to the generic
// category composition and identity owners.
symbol comm_ring_iterated_localization_comparison_left_law
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_comp
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)))
≔ @eq_trans
    (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization))
    (@comm_ring_hom_comp
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison))
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison))
    (@comm_ring_hom_id
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization))
    (@comm_ring_hom_comp_pointwise_path
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison))
    (@eq_trans
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id_pointwise
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_id
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_iterated_localization_comparison_left_law_pointwise
        R f g iterated product_localization comparison)
      (@eq_sym
        (@CommRingHom
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization))
        (@comm_ring_hom_id
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization))
        (@comm_ring_hom_id_pointwise
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization))
        (@comm_ring_hom_id_pointwise_path
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization))));

// Over the first localization map, (forward∘reverse)∘second agrees with the
// original two-stage map. This is the first of the two iterated uniqueness
// steps.
protected symbol comm_ring_iterated_localization_comparison_right_first_agreement
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationAgreement
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_hom_comp_pointwise
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_comparison_forward_map
            R f g iterated product_localization comparison)
          (@comm_ring_iterated_localization_comparison_reverse_map
            R f g iterated product_localization comparison))
        (@comm_ring_iterated_localization_second_map R f g iterated))
      (@comm_ring_iterated_localization_map R f g iterated))
≔ λ x : τ (@comm_ring_carrier R),
    @eq_trans
      (@comm_ring_carrier
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_apply
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_hom_comp_pointwise
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_hom_comp_pointwise
            (@comm_ring_iterated_localization_target R f g iterated)
            (@comm_ring_localization_target
              R (@comm_ring_mul R f g) product_localization)
            (@comm_ring_iterated_localization_target R f g iterated)
            (@comm_ring_iterated_localization_comparison_forward_map
              R f g iterated product_localization comparison)
            (@comm_ring_iterated_localization_comparison_reverse_map
              R f g iterated product_localization comparison))
          (@comm_ring_iterated_localization_second_map R f g iterated))
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_first_map R f g iterated)
          x))
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_localization_map
            R (@comm_ring_mul R f g) product_localization)
          x))
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_map R f g iterated)
        x)
      (@eq_ap
        (@comm_ring_carrier
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization))
        (@comm_ring_carrier
          (@comm_ring_iterated_localization_target R f g iterated))
        (λ y : τ (@comm_ring_carrier
            (@comm_ring_localization_target
              R (@comm_ring_mul R f g) product_localization)),
          @comm_ring_hom_apply
            (@comm_ring_localization_target
              R (@comm_ring_mul R f g) product_localization)
            (@comm_ring_iterated_localization_target R f g iterated)
            (@comm_ring_iterated_localization_comparison_forward_map
              R f g iterated product_localization comparison)
            y)
        (@comm_ring_hom_apply
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_comparison_reverse_map
            R f g iterated product_localization comparison)
          (@comm_ring_hom_apply
            R
            (@comm_ring_iterated_localization_target R f g iterated)
            (@comm_ring_iterated_localization_map R f g iterated)
            x))
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_localization_map
            R (@comm_ring_mul R f g) product_localization)
          x)
        ((@comm_ring_iterated_localization_comparison_reverse_agreement
            R f g iterated product_localization comparison)
          x))
      ((@comm_ring_iterated_localization_comparison_forward_agreement
          R f g iterated product_localization comparison)
        x);

protected symbol comm_ring_iterated_localization_comparison_right_first_composite_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_iterated_localization_map R f g iterated))
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_first_map R f g iterated)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison))
      (@comm_ring_iterated_localization_second_map R f g iterated))
    (@comm_ring_iterated_localization_comparison_right_first_agreement
      R f g iterated product_localization comparison);

protected symbol comm_ring_iterated_localization_comparison_right_first_second_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_iterated_localization_map R f g iterated))
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_first_map R f g iterated)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (λ x : τ (@comm_ring_carrier R),
      @eq_refl
        (@comm_ring_carrier
          (@comm_ring_iterated_localization_target R f g iterated))
        (@comm_ring_hom_apply
          R
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_map R f g iterated)
          x));

protected symbol comm_ring_iterated_localization_comparison_right_first_path
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@=
      (@CommRingHom
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_hom_comp_pointwise
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_comparison_forward_map
            R f g iterated product_localization comparison)
          (@comm_ring_iterated_localization_comparison_reverse_map
            R f g iterated product_localization comparison))
        (@comm_ring_iterated_localization_second_map R f g iterated))
      (@comm_ring_iterated_localization_second_map R f g iterated))
≔ @comm_ring_localization_factor_maps_equal
    R
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_first_map R f g iterated)
    (@comm_ring_iterated_localization_map R f g iterated)
    (@comm_ring_localization_factorization_is_contr
      R f
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_first_map R f g iterated)
      (@comm_ring_localization_property R f
        (@comm_ring_iterated_localization_first R f g iterated))
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_iterated_localization_first_image_unit
        R f g iterated))
    (@comm_ring_iterated_localization_comparison_right_first_composite_factor
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_right_first_second_factor R f g iterated);

// Evaluating the first-stage whole-map equality at an intermediate element
// supplies the second localization triangle.
protected symbol comm_ring_iterated_localization_comparison_right_agreement
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationAgreement
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison))
      (@comm_ring_iterated_localization_second_map R f g iterated))
≔ λ y : τ (@comm_ring_carrier
      (@comm_ring_iterated_localization_intermediate R f g iterated)),
    @eq_ap
      (@CommRingHom
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_carrier
        (@comm_ring_iterated_localization_target R f g iterated))
      (λ h : τ (@CommRingHom
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_target R f g iterated)),
        @comm_ring_hom_apply
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_target R f g iterated)
          h y)
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_iterated_localization_intermediate R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_hom_comp_pointwise
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_localization_target
            R (@comm_ring_mul R f g) product_localization)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_comparison_forward_map
            R f g iterated product_localization comparison)
          (@comm_ring_iterated_localization_comparison_reverse_map
            R f g iterated product_localization comparison))
        (@comm_ring_iterated_localization_second_map R f g iterated))
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_iterated_localization_comparison_right_first_path
        R f g iterated product_localization comparison);

protected symbol comm_ring_iterated_localization_comparison_right_composite_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@CommRingLocalizationFactor
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_iterated_localization_second_map R f g iterated))
≔ @comm_ring_localization_factor_intro
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison))
    (@comm_ring_iterated_localization_comparison_right_agreement
      R f g iterated product_localization comparison);

protected symbol comm_ring_iterated_localization_comparison_right_identity_factor
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  : τ (@CommRingLocalizationFactor
      (@comm_ring_iterated_localization_intermediate R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_iterated_localization_second_map R f g iterated))
≔ @comm_ring_localization_factor_intro
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_hom_id_pointwise
      (@comm_ring_iterated_localization_target R f g iterated))
    (λ y : τ (@comm_ring_carrier
        (@comm_ring_iterated_localization_intermediate R f g iterated)),
      @eq_refl
        (@comm_ring_carrier
          (@comm_ring_iterated_localization_target R f g iterated))
        (@comm_ring_hom_apply
          (@comm_ring_iterated_localization_intermediate R f g iterated)
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_second_map R f g iterated)
          y));

protected symbol comm_ring_iterated_localization_comparison_right_law_pointwise
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@=
      (@CommRingHom
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id_pointwise
        (@comm_ring_iterated_localization_target R f g iterated)))
≔ @comm_ring_localization_factor_maps_equal
    (@comm_ring_iterated_localization_intermediate R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
    (@comm_ring_iterated_localization_second_map R f g iterated)
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
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_second_map R f g iterated)
      (@comm_ring_localization_inverted_unit
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
          (@comm_ring_iterated_localization_second R f g iterated))))
    (@comm_ring_iterated_localization_comparison_right_composite_factor
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_right_identity_factor R f g iterated);

symbol comm_ring_iterated_localization_comparison_right_law
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@=
      (@CommRingHom
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_comp
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id
        (@comm_ring_iterated_localization_target R f g iterated)))
≔ @eq_trans
    (@CommRingHom
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_target R f g iterated))
    (@comm_ring_hom_comp
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison))
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison))
    (@comm_ring_hom_id
      (@comm_ring_iterated_localization_target R f g iterated))
    (@comm_ring_hom_comp_pointwise_path
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison))
    (@eq_trans
      (@CommRingHom
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id_pointwise
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_id
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_iterated_localization_comparison_right_law_pointwise
        R f g iterated product_localization comparison)
      (@eq_sym
        (@CommRingHom
          (@comm_ring_iterated_localization_target R f g iterated)
          (@comm_ring_iterated_localization_target R f g iterated))
        (@comm_ring_hom_id
          (@comm_ring_iterated_localization_target R f g iterated))
        (@comm_ring_hom_id_pointwise
          (@comm_ring_iterated_localization_target R f g iterated))
        (@comm_ring_hom_id_pointwise_path
          (@comm_ring_iterated_localization_target R f g iterated))));

// The comparison is therefore a whole internal omega-equivalence in the
// category of commutative rings. The same reverse map serves both inverse
// slots; the cancellation laws are equalities of whole structured maps.
symbol comm_ring_iterated_localization_comparison_omega_equiv_along
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@OmegaEquivAlong
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison))
≔ @omega_equiv_along_intro
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_left_law
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_right_law
      R f g iterated product_localization comparison);

// Derived first-class facade with the same selected forward comparison.
symbol comm_ring_iterated_localization_comparison_omega_equiv
  [R : τ CommRing]
  [f g : τ (@comm_ring_carrier R)]
  [iterated : τ (@CommRingIteratedLocalizationAt R f g)]
  [product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))]
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization))
  : τ (@OmegaEquiv
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated))
≔ @omega_equiv_pack
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_omega_equiv_along
      R f g iterated product_localization comparison);
