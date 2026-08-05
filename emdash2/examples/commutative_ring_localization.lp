/*
  Reviewer-facing PSSS-07a example: universal-property-first localization,
  with a constructive nonempty model and no fraction representation.
*/

require open emdash.emdash3_2_commutative_algebra_localization;

// The public boundary exposes explicit units and pointwise factor triangles.
assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @CommRingUnitEvidence R x
  : Grpd;

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_unit_evidence_is_prop R x
  : τ (IsPropGrpd (@CommRingUnitEvidence R x));

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  (u v : τ (@CommRingUnitEvidence R x)) ⊢
  @comm_ring_unit_inverse_unique R x u v
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v));

assert (R L S : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  (factor : τ (@CommRingHom L S))
  (h : τ (@CommRingHom R S)) ⊢
  @CommRingLocalizationAgreement R L S localization_map factor h
  : Grpd;

assert (R L S : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  (factor : τ (@CommRingHom L S))
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_localization_agreement_is_prop
    R L S localization_map factor h
  : τ (IsPropGrpd
      (@CommRingLocalizationAgreement R L S localization_map factor h));

assert (R : τ CommRing)
  (f : τ (@comm_ring_carrier R)) ⊢
  @CommRingLocalizationAt R f
  : Grpd;

// Localization's first concrete consumer justifies structured-map
// extensionality in the ring-morphism layer.
assert (R S : τ CommRing)
  (h k : τ (@CommRingHom R S))
  (p : τ (@CommRingHomPointwisePath R S h k)) ⊢
  @comm_ring_hom_ext R S h k p
  : τ (h = k);

// The explicit unique endomorphism of the zero ring is the structure map.
symbol zero_localization_map_laws
  : τ (@CommRingHomLaws
      zero_comm_ring
      zero_comm_ring
      (λ _ : τ Unit_grpd, tt))
≔ @comm_ring_hom_laws_intro
    zero_comm_ring
    zero_comm_ring
    (λ _ : τ Unit_grpd, tt)
    (@eq_refl Unit_grpd tt)
    (@eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd, @eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt);

symbol zero_localization_map
  : τ (@CommRingHom zero_comm_ring zero_comm_ring)
≔ @comm_ring_hom_intro
    zero_comm_ring
    zero_comm_ring
    (λ _ : τ Unit_grpd, tt)
    zero_localization_map_laws;

// Its selected element maps to the unique unit of the zero ring.
symbol zero_localization_unit
  : τ (@CommRingUnitEvidence
      zero_comm_ring
      (@comm_ring_hom_apply
        zero_comm_ring zero_comm_ring zero_localization_map tt))
≔ @comm_ring_unit_intro
    zero_comm_ring
    (@comm_ring_hom_apply
      zero_comm_ring zero_comm_ring zero_localization_map tt)
    tt
    (@eq_refl Unit_grpd tt);

assert ⊢ @comm_ring_unit_inverse
    zero_comm_ring
    (@comm_ring_hom_apply
      zero_comm_ring zero_comm_ring zero_localization_map tt)
    zero_localization_unit
  ≡ tt;

assert ⊢ @comm_ring_unit_law
    zero_comm_ring
    (@comm_ring_hom_apply
      zero_comm_ring zero_comm_ring zero_localization_map tt)
    zero_localization_unit
  ≡ @eq_refl Unit_grpd tt;

// The original map factors through the zero-ring structure map by Unit
// contractibility; no projected generic identity computation is needed.
symbol zero_localization_center_agreement
  [S : τ CommRing]
  (h : τ (@CommRingHom zero_comm_ring S))
  : τ (@CommRingLocalizationAgreement
      zero_comm_ring zero_comm_ring S
      zero_localization_map h h)
≔ λ x : τ Unit_grpd,
    @eq_ap
      Unit_grpd
      (@comm_ring_carrier S)
      (@comm_ring_hom_function zero_comm_ring S h)
      tt x
      (@is_contr_path Unit_grpd unit_is_contr x);

symbol zero_localization_factor_center
  [S : τ CommRing]
  (h : τ (@CommRingHom zero_comm_ring S))
  : τ (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h)
≔ @comm_ring_localization_factor_intro
    zero_comm_ring zero_comm_ring S zero_localization_map h
    h
    (@zero_localization_center_agreement S h);

assert (S : τ CommRing)
  (h : τ (@CommRingHom zero_comm_ring S)) ⊢
  @comm_ring_localization_factor_map
    zero_comm_ring zero_comm_ring S zero_localization_map h
    (@zero_localization_factor_center S h)
  ≡ h;

// A competitor triangle identifies its map pointwise with the centre: first
// reverse the triangle at x, then move its Unit input from tt to x.
symbol zero_localization_competitor_pointwise
  [S : τ CommRing]
  [h : τ (@CommRingHom zero_comm_ring S)]
  (candidate : τ (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h))
  : τ (@CommRingHomPointwisePath
      zero_comm_ring S h
      (@comm_ring_localization_factor_map
        zero_comm_ring zero_comm_ring S zero_localization_map h candidate))
≔ λ x : τ Unit_grpd,
    @eq_trans
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply zero_comm_ring S h x)
      (@comm_ring_hom_apply zero_comm_ring S
        (@comm_ring_localization_factor_map
          zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
        tt)
      (@comm_ring_hom_apply zero_comm_ring S
        (@comm_ring_localization_factor_map
          zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
        x)
      (@eq_sym
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply zero_comm_ring S
          (@comm_ring_localization_factor_map
            zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
          tt)
        (@comm_ring_hom_apply zero_comm_ring S h x)
        ((@comm_ring_localization_factor_agreement
            zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
          x))
      (@eq_ap
        Unit_grpd
        (@comm_ring_carrier S)
        (@comm_ring_hom_function zero_comm_ring S
          (@comm_ring_localization_factor_map
            zero_comm_ring zero_comm_ring S zero_localization_map h candidate))
        tt x
        (@is_contr_path Unit_grpd unit_is_contr x));

symbol zero_localization_factor_map_path
  [S : τ CommRing]
  [h : τ (@CommRingHom zero_comm_ring S)]
  (candidate : τ (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h))
  : τ (h = @comm_ring_localization_factor_map
      zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
≔ @comm_ring_hom_ext
    zero_comm_ring S
    h
    (@comm_ring_localization_factor_map
      zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
    (@zero_localization_competitor_pointwise S h candidate);

// The map path and the unique property-valued fibre path form the full Sigma
// equality from the selected factor to any competitor.
symbol zero_localization_factor_path
  [S : τ CommRing]
  [h : τ (@CommRingHom zero_comm_ring S)]
  (candidate : τ (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h))
  : τ (@= (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h)
      (@zero_localization_factor_center S h)
      candidate)
≔ @Struct_sigma
    (@= (@CommRingHom zero_comm_ring S)
      h
      (@comm_ring_localization_factor_map
        zero_comm_ring zero_comm_ring S zero_localization_map h candidate))
    (λ p : τ (@= (@CommRingHom zero_comm_ring S)
        h
        (@comm_ring_localization_factor_map
          zero_comm_ring zero_comm_ring S zero_localization_map h candidate)),
      @PathOver
        (@CommRingHom zero_comm_ring S)
        (λ factor : τ (@CommRingHom zero_comm_ring S),
          @CommRingLocalizationAgreement
            zero_comm_ring zero_comm_ring S
            zero_localization_map factor h)
        h
        (@comm_ring_localization_factor_map
          zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
        p
        (@zero_localization_center_agreement S h)
        (@comm_ring_localization_factor_agreement
          zero_comm_ring zero_comm_ring S zero_localization_map h candidate))
    (@zero_localization_factor_map_path S h candidate)
    (@comm_ring_localization_agreement_pathover
      zero_comm_ring zero_comm_ring S
      zero_localization_map h
      h
      (@comm_ring_localization_factor_map
        zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
      (@zero_localization_center_agreement S h)
      (@comm_ring_localization_factor_agreement
        zero_comm_ring zero_comm_ring S zero_localization_map h candidate)
      (@zero_localization_factor_map_path S h candidate));

// Hence every admissible zero-ring factorization space is contractible.
symbol zero_localization_factor_is_contr
  (S : τ CommRing)
  (h : τ (@CommRingHom zero_comm_ring S))
  : τ (IsContr (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h))
≔ @Struct_sigma
    (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h)
    (λ centre : τ (@CommRingLocalizationFactor
        zero_comm_ring zero_comm_ring S zero_localization_map h),
      @Pi_grpd
        (@CommRingLocalizationFactor
          zero_comm_ring zero_comm_ring S zero_localization_map h)
        (λ candidate : τ (@CommRingLocalizationFactor
            zero_comm_ring zero_comm_ring S zero_localization_map h),
          @= (@CommRingLocalizationFactor
            zero_comm_ring zero_comm_ring S zero_localization_map h)
            centre candidate))
    (@zero_localization_factor_center S h)
    (λ candidate : τ (@CommRingLocalizationFactor
        zero_comm_ring zero_comm_ring S zero_localization_map h),
      @zero_localization_factor_path S h candidate);

// The zero ring localized at its unique element is itself. The admissibility
// witness for h is intentionally unused: every structured zero-ring map has
// the displayed unique factor through the chosen structure map.
symbol zero_is_localization_at_point
  : τ (@IsCommRingLocalizationAt
      zero_comm_ring tt zero_comm_ring zero_localization_map)
≔ @comm_ring_localization_property_intro
    zero_comm_ring tt zero_comm_ring zero_localization_map
    zero_localization_unit
    (λ S : τ CommRing,
      λ h : τ (@CommRingHom zero_comm_ring S),
        λ _ : τ (@CommRingUnitEvidence S
            (@comm_ring_hom_apply zero_comm_ring S h tt)),
          @zero_localization_factor_is_contr S h);

symbol zero_localization_at_point
  : τ (@CommRingLocalizationAt zero_comm_ring tt)
≔ @comm_ring_localization_intro
    zero_comm_ring tt
    zero_comm_ring
    zero_localization_map
    zero_is_localization_at_point;

assert ⊢ zero_localization_at_point
  : τ (@CommRingLocalizationAt zero_comm_ring tt);

assert ⊢ @comm_ring_localization_target
    zero_comm_ring tt zero_localization_at_point
  ≡ zero_comm_ring;

assert ⊢
  @comm_ring_hom_apply
    zero_comm_ring
    zero_comm_ring
    (@comm_ring_localization_map
      zero_comm_ring tt zero_localization_at_point)
    tt
  ≡ tt;

assert (S : τ CommRing)
  (h : τ (@CommRingHom zero_comm_ring S)) ⊢
  @zero_localization_factor_is_contr S h
  : τ (IsContr (@CommRingLocalizationFactor
      zero_comm_ring zero_comm_ring S zero_localization_map h));

// The localization package remains an honest Sigma package; no broad eta
// reduction is added for an opaque chosen localization.
assertnot (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (localization : τ (@CommRingLocalizationAt R f)) ⊢
  localization
  ≡ @comm_ring_localization_intro
      R f
      (@comm_ring_localization_target R f localization)
      (@comm_ring_localization_map R f localization)
      (@comm_ring_localization_property R f localization);
