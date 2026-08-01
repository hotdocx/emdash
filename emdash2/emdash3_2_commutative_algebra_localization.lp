/*
  Universal-property-first localization of commutative rings.

  This one-way standard-library module packages a chosen target ring, a
  structure map that inverts one selected element, and contractible
  factorization through that map. Factor triangles are stated pointwise on
  carrier functions, so the interface does not require projected computation
  for opaque generic CommRing_cat identities or composites. No fraction,
  exponent, finite-family, power, or polynomial representation is selected.
*/

require open emdash.emdash3_2_commutative_algebra_category;

// Explicit inverse evidence for one element; no fraction representation.
symbol CommRingUnitEvidence
  [R : τ CommRing]
  (x : τ (@comm_ring_carrier R))
  : Grpd
≔ `Σ_ inverse : τ (@comm_ring_carrier R),
    @= (@comm_ring_carrier R)
      (@comm_ring_mul R x inverse)
      (@comm_ring_one R);

symbol comm_ring_unit_intro
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (inverse : τ (@comm_ring_carrier R))
  (law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x inverse)
      (@comm_ring_one R)))
  : τ (@CommRingUnitEvidence R x)
≔ @Struct_sigma
    (@comm_ring_carrier R)
    (λ y : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier R)
        (@comm_ring_mul R x y)
        (@comm_ring_one R))
    inverse
    law;

symbol comm_ring_unit_inverse
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x))
  : τ (@comm_ring_carrier R)
≔ sigma_Fst u;

symbol comm_ring_unit_law
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
      (@comm_ring_one R))
≔ sigma_Snd u;

/*
  Uniqueness of inverse evidence.

  The protected six-step chain is the standard commutative-monoid proof

    y = y*1 = y*(x*z) = (y*x)*z = (x*y)*z = 1*z = z.

  Carrier sethood then makes the base inverse path contractible, and the
  multiplication-law PathOver is contractible for the same reason. Thus the
  complete Sigma witness is proposition-valued, as required by semantic
  invertibility predicates in downstream sieve constructions.
*/
protected symbol comm_ring_unit_inverse_unique_step1
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_mul R
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_one R)))
≔ @eq_sym
    (@comm_ring_carrier R)
    (@comm_ring_mul R
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_one R))
    (@comm_ring_unit_inverse R x u)
    ((@comm_ring_mul_one_law R)
      (@comm_ring_unit_inverse R x u));

protected symbol comm_ring_unit_inverse_unique_step2
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_one R))
      (@comm_ring_mul R
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_mul R x (@comm_ring_unit_inverse R x v))))
≔ @eq_ap
    (@comm_ring_carrier R)
    (@comm_ring_carrier R)
    (λ z : τ (@comm_ring_carrier R),
      @comm_ring_mul R (@comm_ring_unit_inverse R x u) z)
    (@comm_ring_one R)
    (@comm_ring_mul R x (@comm_ring_unit_inverse R x v))
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_mul R x (@comm_ring_unit_inverse R x v))
      (@comm_ring_one R)
      (@comm_ring_unit_law R x v));

protected symbol comm_ring_unit_inverse_unique_step3
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_mul R x (@comm_ring_unit_inverse R x v)))
      (@comm_ring_mul R
        (@comm_ring_mul R (@comm_ring_unit_inverse R x u) x)
        (@comm_ring_unit_inverse R x v)))
≔ @eq_sym
    (@comm_ring_carrier R)
    (@comm_ring_mul R
      (@comm_ring_mul R (@comm_ring_unit_inverse R x u) x)
      (@comm_ring_unit_inverse R x v))
    (@comm_ring_mul R
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_mul R x (@comm_ring_unit_inverse R x v)))
    ((@comm_ring_mul_assoc_law R)
      (@comm_ring_unit_inverse R x u)
      x
      (@comm_ring_unit_inverse R x v));

protected symbol comm_ring_unit_inverse_unique_step4
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_mul R (@comm_ring_unit_inverse R x u) x)
        (@comm_ring_unit_inverse R x v))
      (@comm_ring_mul R
        (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
        (@comm_ring_unit_inverse R x v)))
≔ @eq_ap
    (@comm_ring_carrier R)
    (@comm_ring_carrier R)
    (λ z : τ (@comm_ring_carrier R),
      @comm_ring_mul R z (@comm_ring_unit_inverse R x v))
    (@comm_ring_mul R (@comm_ring_unit_inverse R x u) x)
    (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
    ((@comm_ring_mul_comm_law R)
      (@comm_ring_unit_inverse R x u)
      x);

protected symbol comm_ring_unit_inverse_unique_step5
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
        (@comm_ring_unit_inverse R x v))
      (@comm_ring_mul R
        (@comm_ring_one R)
        (@comm_ring_unit_inverse R x v)))
≔ @eq_ap
    (@comm_ring_carrier R)
    (@comm_ring_carrier R)
    (λ z : τ (@comm_ring_carrier R),
      @comm_ring_mul R z (@comm_ring_unit_inverse R x v))
    (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
    (@comm_ring_one R)
    (@comm_ring_unit_law R x u);

protected symbol comm_ring_unit_inverse_unique_step6
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_one R)
        (@comm_ring_unit_inverse R x v))
      (@comm_ring_unit_inverse R x v))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R
      (@comm_ring_one R)
      (@comm_ring_unit_inverse R x v))
    (@comm_ring_mul R
      (@comm_ring_unit_inverse R x v)
      (@comm_ring_one R))
    (@comm_ring_unit_inverse R x v)
    ((@comm_ring_mul_comm_law R)
      (@comm_ring_one R)
      (@comm_ring_unit_inverse R x v))
    ((@comm_ring_mul_one_law R)
      (@comm_ring_unit_inverse R x v));

symbol comm_ring_unit_inverse_unique
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_unit_inverse R x u)
    (@comm_ring_mul R
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_one R))
    (@comm_ring_unit_inverse R x v)
    (@comm_ring_unit_inverse_unique_step1 R x u v)
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_one R))
      (@comm_ring_mul R
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_mul R x (@comm_ring_unit_inverse R x v)))
      (@comm_ring_unit_inverse R x v)
      (@comm_ring_unit_inverse_unique_step2 R x u v)
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_mul R
          (@comm_ring_unit_inverse R x u)
          (@comm_ring_mul R x (@comm_ring_unit_inverse R x v)))
        (@comm_ring_mul R
          (@comm_ring_mul R (@comm_ring_unit_inverse R x u) x)
          (@comm_ring_unit_inverse R x v))
        (@comm_ring_unit_inverse R x v)
        (@comm_ring_unit_inverse_unique_step3 R x u v)
        (@eq_trans
          (@comm_ring_carrier R)
          (@comm_ring_mul R
            (@comm_ring_mul R (@comm_ring_unit_inverse R x u) x)
            (@comm_ring_unit_inverse R x v))
          (@comm_ring_mul R
            (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
            (@comm_ring_unit_inverse R x v))
          (@comm_ring_unit_inverse R x v)
          (@comm_ring_unit_inverse_unique_step4 R x u v)
          (@eq_trans
            (@comm_ring_carrier R)
            (@comm_ring_mul R
              (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
              (@comm_ring_unit_inverse R x v))
            (@comm_ring_mul R
              (@comm_ring_one R)
              (@comm_ring_unit_inverse R x v))
            (@comm_ring_unit_inverse R x v)
            (@comm_ring_unit_inverse_unique_step5 R x u v)
            (@comm_ring_unit_inverse_unique_step6 R x u v)))));

protected symbol comm_ring_unit_inverse_path_is_contr
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (IsContr (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v)))
≔ @Struct_sigma
    (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v))
    (λ centre : τ (@= (@comm_ring_carrier R)
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_unit_inverse R x v)),
      @Pi_grpd
        (@= (@comm_ring_carrier R)
          (@comm_ring_unit_inverse R x u)
          (@comm_ring_unit_inverse R x v))
        (λ p : τ (@= (@comm_ring_carrier R)
            (@comm_ring_unit_inverse R x u)
            (@comm_ring_unit_inverse R x v)),
          @= (@= (@comm_ring_carrier R)
            (@comm_ring_unit_inverse R x u)
            (@comm_ring_unit_inverse R x v))
            centre p))
    (@comm_ring_unit_inverse_unique R x u v)
    (λ p : τ (@= (@comm_ring_carrier R)
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_unit_inverse R x v)),
      @is_contr_center
        (@= (@= (@comm_ring_carrier R)
          (@comm_ring_unit_inverse R x u)
          (@comm_ring_unit_inverse R x v))
          (@comm_ring_unit_inverse_unique R x u v)
          p)
        ((@comm_ring_carrier_is_set R
            (@comm_ring_unit_inverse R x u)
            (@comm_ring_unit_inverse R x v))
          (@comm_ring_unit_inverse_unique R x u v)
          p));

protected symbol comm_ring_unit_law_pathover_is_contr
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  (p : τ (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v)))
  : τ (IsContr (@PathOver
      (@comm_ring_carrier R)
      (λ inverse : τ (@comm_ring_carrier R),
        @= (@comm_ring_carrier R)
          (@comm_ring_mul R x inverse)
          (@comm_ring_one R))
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v)
      p
      (@comm_ring_unit_law R x u)
      (@comm_ring_unit_law R x v)))
≔ (@comm_ring_carrier_is_set R
      (@comm_ring_mul R x (@comm_ring_unit_inverse R x u))
      (@comm_ring_one R))
    (@comm_ring_unit_law R x u)
    (@ind_eq
      (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v)
      p
      (λ inverse : τ (@comm_ring_carrier R),
        @= (@comm_ring_carrier R)
          (@comm_ring_mul R x inverse)
          (@comm_ring_one R))
      (@comm_ring_unit_law R x v));

protected symbol comm_ring_unit_equality_is_contr
  [R : τ CommRing]
  [x : τ (@comm_ring_carrier R)]
  (u v : τ (@CommRingUnitEvidence R x))
  : τ (IsContr (@= (@CommRingUnitEvidence R x) u v))
≔ @is_contr_sigma
    (@= (@comm_ring_carrier R)
      (@comm_ring_unit_inverse R x u)
      (@comm_ring_unit_inverse R x v))
    (λ p : τ (@= (@comm_ring_carrier R)
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_unit_inverse R x v)),
      @PathOver
        (@comm_ring_carrier R)
        (λ inverse : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier R)
            (@comm_ring_mul R x inverse)
            (@comm_ring_one R))
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_unit_inverse R x v)
        p
        (@comm_ring_unit_law R x u)
        (@comm_ring_unit_law R x v))
    (@comm_ring_unit_inverse_path_is_contr R x u v)
    (λ p : τ (@= (@comm_ring_carrier R)
        (@comm_ring_unit_inverse R x u)
        (@comm_ring_unit_inverse R x v)),
      @comm_ring_unit_law_pathover_is_contr R x u v p);

symbol comm_ring_unit_evidence_is_prop
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (IsPropGrpd (@CommRingUnitEvidence R x))
≔ λ u : τ (@CommRingUnitEvidence R x),
    λ v : τ (@CommRingUnitEvidence R x),
      @comm_ring_unit_equality_is_contr R x u v;

/*
  Functorial unit evidence.

  Path transport and preservation by a structured ring homomorphism belong
  with the semantic unit classifier itself.  They are used both by iterated
  localization and by the ring-valued-presheaf invertibility predicate.  The
  explicit inverse selected by `comm_ring_hom_preserves_unit` computes to the
  image of the input inverse; no category-composition rule is involved.
*/
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

// Pointwise agreement of a candidate factor with the original ring map.
symbol CommRingLocalizationAgreement
  [R L S : τ CommRing]
  (localization_map : τ (@CommRingHom R L))
  (factor : τ (@CommRingHom L S))
  (h : τ (@CommRingHom R S))
  : Grpd
≔ @Pi_grpd
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier S)
        (@comm_ring_hom_apply L S factor
          (@comm_ring_hom_apply R L localization_map x))
        (@comm_ring_hom_apply R S h x));

symbol comm_ring_localization_agreement_is_prop
  [R L S : τ CommRing]
  (localization_map : τ (@CommRingHom R L))
  (factor : τ (@CommRingHom L S))
  (h : τ (@CommRingHom R S))
  : τ (IsPropGrpd
      (@CommRingLocalizationAgreement R L S localization_map factor h))
≔ @is_prop_pi
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier S)
        (@comm_ring_hom_apply L S factor
          (@comm_ring_hom_apply R L localization_map x))
        (@comm_ring_hom_apply R S h x))
    (λ x : τ (@comm_ring_carrier R),
      (@comm_ring_carrier_is_set S)
        (@comm_ring_hom_apply L S factor
          (@comm_ring_hom_apply R L localization_map x))
        (@comm_ring_hom_apply R S h x));

// A factor is a structured map together with its pointwise triangle.
symbol CommRingLocalizationFactor
  [R L S : τ CommRing]
  (localization_map : τ (@CommRingHom R L))
  (h : τ (@CommRingHom R S))
  : Grpd
≔ `Σ_ factor : τ (@CommRingHom L S),
    @CommRingLocalizationAgreement R L S localization_map factor h;

symbol comm_ring_localization_factor_intro
  [R L S : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  [h : τ (@CommRingHom R S)]
  (factor : τ (@CommRingHom L S))
  (agreement : τ (@CommRingLocalizationAgreement
      R L S localization_map factor h))
  : τ (@CommRingLocalizationFactor R L S localization_map h)
≔ @Struct_sigma
    (@CommRingHom L S)
    (λ k : τ (@CommRingHom L S),
      @CommRingLocalizationAgreement R L S localization_map k h)
    factor
    agreement;

symbol comm_ring_localization_factor_map
  [R L S : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  [h : τ (@CommRingHom R S)]
  (factor : τ (@CommRingLocalizationFactor R L S localization_map h))
  : τ (@CommRingHom L S)
≔ sigma_Fst factor;

symbol comm_ring_localization_factor_agreement
  [R L S : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  [h : τ (@CommRingHom R S)]
  (factor : τ (@CommRingLocalizationFactor R L S localization_map h))
  : τ (@CommRingLocalizationAgreement
      R L S localization_map
      (@comm_ring_localization_factor_map R L S localization_map h factor)
      h)
≔ sigma_Snd factor;

// The selected map inverts f and has a contractible factorization space.
symbol IsCommRingLocalizationAt
  [R : τ CommRing]
  (f : τ (@comm_ring_carrier R))
  (L : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  : Grpd
≔ @Product_grpd
    (@CommRingUnitEvidence L
      (@comm_ring_hom_apply R L localization_map f))
    (@Pi_grpd CommRing
      (λ S : τ CommRing,
        @Pi_grpd (@CommRingHom R S)
          (λ h : τ (@CommRingHom R S),
            @Pi_grpd
              (@CommRingUnitEvidence S
                (@comm_ring_hom_apply R S h f))
              (λ _ : τ (@CommRingUnitEvidence S
                  (@comm_ring_hom_apply R S h f)),
                IsContr (@CommRingLocalizationFactor
                  R L S localization_map h)))));

symbol comm_ring_localization_property_intro
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  [L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (inverts : τ (@CommRingUnitEvidence L
      (@comm_ring_hom_apply R L localization_map f)))
  (universal : τ (@Pi_grpd CommRing
      (λ S : τ CommRing,
        @Pi_grpd (@CommRingHom R S)
          (λ h : τ (@CommRingHom R S),
            @Pi_grpd
              (@CommRingUnitEvidence S
                (@comm_ring_hom_apply R S h f))
              (λ _ : τ (@CommRingUnitEvidence S
                  (@comm_ring_hom_apply R S h f)),
                IsContr (@CommRingLocalizationFactor
                  R L S localization_map h))))))
  : τ (@IsCommRingLocalizationAt R f L localization_map)
≔ @Product_pair_grpd
    (@CommRingUnitEvidence L
      (@comm_ring_hom_apply R L localization_map f))
    (@Pi_grpd CommRing
      (λ S : τ CommRing,
        @Pi_grpd (@CommRingHom R S)
          (λ h : τ (@CommRingHom R S),
            @Pi_grpd
              (@CommRingUnitEvidence S
                (@comm_ring_hom_apply R S h f))
              (λ _ : τ (@CommRingUnitEvidence S
                  (@comm_ring_hom_apply R S h f)),
                IsContr (@CommRingLocalizationFactor
                  R L S localization_map h)))))
    inverts universal;

symbol comm_ring_localization_inverted_unit
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  [L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (property : τ (@IsCommRingLocalizationAt R f L localization_map))
  : τ (@CommRingUnitEvidence L
      (@comm_ring_hom_apply R L localization_map f))
≔ sigma_Fst property;

symbol comm_ring_localization_factorization_is_contr
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  [L : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  (property : τ (@IsCommRingLocalizationAt R f L localization_map))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (inverts : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h f)))
  : τ (IsContr (@CommRingLocalizationFactor
      R L S localization_map h))
≔ sigma_Snd property S h inverts;

// Chosen localizations package their target, structure map, and universal data.
symbol CommRingLocalizationAt
  (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  : Grpd
≔ `Σ_ L : τ CommRing,
   `Σ_ localization_map : τ (@CommRingHom R L),
       @IsCommRingLocalizationAt R f L localization_map;

symbol comm_ring_localization_intro
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (L : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  (property : τ (@IsCommRingLocalizationAt R f L localization_map))
  : τ (@CommRingLocalizationAt R f)
≔ @Struct_sigma
    CommRing
    (λ T : τ CommRing,
      `Σ_ iota : τ (@CommRingHom R T),
          @IsCommRingLocalizationAt R f T iota)
    L
    (@Struct_sigma
      (@CommRingHom R L)
      (λ iota : τ (@CommRingHom R L),
        @IsCommRingLocalizationAt R f L iota)
      localization_map
      property);

symbol comm_ring_localization_target
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  : τ CommRing
≔ sigma_Fst localization;

symbol comm_ring_localization_map
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  : τ (@CommRingHom R
      (@comm_ring_localization_target R f localization))
≔ sigma_Fst (sigma_Snd localization);

symbol comm_ring_localization_property
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  : τ (@IsCommRingLocalizationAt
      R f
      (@comm_ring_localization_target R f localization)
      (@comm_ring_localization_map R f localization))
≔ sigma_Snd (sigma_Snd localization);

// Property-valued factor-agreement fibres transport uniquely along a map path.
symbol comm_ring_localization_agreement_pathover
  [R L S : τ CommRing]
  [localization_map : τ (@CommRingHom R L)]
  [h : τ (@CommRingHom R S)]
  [factor0 factor1 : τ (@CommRingHom L S)]
  (agreement0 : τ (@CommRingLocalizationAgreement
      R L S localization_map factor0 h))
  (agreement1 : τ (@CommRingLocalizationAgreement
      R L S localization_map factor1 h))
  (p : τ (factor0 = factor1))
  : τ (@PathOver
      (@CommRingHom L S)
      (λ factor : τ (@CommRingHom L S),
        @CommRingLocalizationAgreement
          R L S localization_map factor h)
      factor0 factor1 p agreement0 agreement1)
≔ @ind_eqr
    (@CommRingHom L S)
    factor1
    (λ factor : τ (@CommRingHom L S),
      λ q : τ (factor = factor1),
        @Pi_grpd
          (@CommRingLocalizationAgreement
            R L S localization_map factor h)
          (λ evidence : τ (@CommRingLocalizationAgreement
              R L S localization_map factor h),
            @PathOver
              (@CommRingHom L S)
              (λ k : τ (@CommRingHom L S),
                @CommRingLocalizationAgreement
                  R L S localization_map k h)
              factor factor1 q evidence agreement1))
    (λ evidence : τ (@CommRingLocalizationAgreement
        R L S localization_map factor1 h),
      @is_contr_center
        (@= (@CommRingLocalizationAgreement
          R L S localization_map factor1 h)
          evidence agreement1)
        ((@comm_ring_localization_agreement_is_prop
            R L S localization_map factor1 h)
          evidence agreement1))
    factor0
    p
    agreement0;
