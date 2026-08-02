/*
  Computational affine functor of points and basic-open representation.

  The affine functor of points is the existing Yoneda presheaf on
  CommRing_cat^op.  Its value at S is the whole structured-map classifier
  CommRingHom(R,S), with object and arrow action retained by the generic
  internal-hom owners.  The basic open D(f) is the already-internal semantic
  invertibility sieve for the shared identity CommRing-valued presheaf.

  For a selected localization i:R->R[1/f], its universal property constructs
  a TypeEquiv between maps R[1/f]->S and D(f)-points (h:R->S together with
  unit evidence for h(f)).  Both inverse paths are derived from localization
  contractibility, CommRing extensionality, and proposition-valued unit
  evidence.  No univalence, whole-functor equality, external naturality
  family, rewrite rule, or unification rule is introduced.

  This is a componentwise representability theorem between two objects that
  already retain their functorial action internally.  It does not yet claim a
  whole natural equivalence of presheaves, a topology, sheafhood, or a general
  scheme.
*/

require open emdash.emdash3_2_commutative_algebra_presheaves;
require open emdash.emdash3_2_sites;

// The affine functor of points is the existing Yoneda presheaf on Aff.
symbol affine_spec_functor_of_points
  (R : τ CommRing)
  : τ (@Psh (Op_cat CommRing_cat))
≔ @yoneda_psh (Op_cat CommRing_cat) R;

// Its S-points are whole structured maps R -> S.
symbol AffineSpecPoint
  (R S : τ CommRing)
  : Grpd
≔ Obj (@Fibre_cat
    CommRing_cat
    (@affine_spec_functor_of_points R)
    S);

// D(f) is the already-internal semantic invertibility sieve for the identity
// CommRing-valued presheaf; it retains all restriction action generically.
symbol affine_spec_basic_open_sieve
  [R : τ CommRing]
  (f : τ (@comm_ring_carrier R))
  : τ (@Sieve (Op_cat CommRing_cat) R)
≔ @comm_ring_psh_invertibility_sieve
    (Op_cat CommRing_cat)
    affine_comm_ring_psh
    R f;

// An S-point of D(f) is a ring map h:R->S together with actual unit evidence
// for h(f).  The evidence field is the fibre of the internal sieve above.
symbol AffineSpecBasicOpenPoint
  [R : τ CommRing]
  (f : τ (@comm_ring_carrier R))
  (S : τ CommRing)
  : Grpd
≔ `Σ_ h : τ (@AffineSpecPoint R S),
    @SieveMembership
      (Op_cat CommRing_cat)
      R
      (@affine_spec_basic_open_sieve R f)
      (Struct_sigma S h);

symbol affine_spec_basic_open_point_intro
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h f)))
  : τ (@AffineSpecBasicOpenPoint R f S)
≔ @Struct_sigma
    (@CommRingHom R S)
    (λ k : τ (@CommRingHom R S),
      @CommRingUnitEvidence S (@comm_ring_hom_apply R S k f))
    h unit;

symbol affine_spec_basic_open_point_map
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S))
  : τ (@CommRingHom R S)
≔ sigma_Fst p;

symbol affine_spec_basic_open_point_unit
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S))
  : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S
        (@affine_spec_basic_open_point_map R f S p)
        f))
≔ sigma_Snd p;

// A map out of a selected localization gives a D(f)-point by precomposition.
symbol affine_spec_basic_open_point_from_localized_map
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S))
  : τ (@AffineSpecBasicOpenPoint R f S)
≔ @affine_spec_basic_open_point_intro
    R f S
    (@comm_ring_hom_comp_pointwise
      R
      (@comm_ring_localization_target R f localization)
      S
      k
      (@comm_ring_localization_map R f localization))
    (@comm_ring_hom_preserves_unit
      (@comm_ring_localization_target R f localization)
      S
      k
      (@comm_ring_hom_apply
        R
        (@comm_ring_localization_target R f localization)
        (@comm_ring_localization_map R f localization)
        f)
      (@comm_ring_localization_inverted_unit
        R f
        (@comm_ring_localization_target R f localization)
        (@comm_ring_localization_map R f localization)
        (@comm_ring_localization_property R f localization)));

// Conversely, localization contractibility selects the unique factor map.
symbol affine_spec_basic_open_point_factor
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R f localization)
      S
      (@comm_ring_localization_map R f localization)
      (@affine_spec_basic_open_point_map R f S p))
≔ @is_contr_center
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R f localization)
      S
      (@comm_ring_localization_map R f localization)
      (@affine_spec_basic_open_point_map R f S p))
    (@comm_ring_localization_factorization_is_contr
      R f
      (@comm_ring_localization_target R f localization)
      (@comm_ring_localization_map R f localization)
      (@comm_ring_localization_property R f localization)
      S
      (@affine_spec_basic_open_point_map R f S p)
      (@affine_spec_basic_open_point_unit R f S p));

symbol affine_spec_basic_open_point_lift
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S))
  : τ (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S)
≔ @comm_ring_localization_factor_map
    R
    (@comm_ring_localization_target R f localization)
    S
    (@comm_ring_localization_map R f localization)
    (@affine_spec_basic_open_point_map R f S p)
    (@affine_spec_basic_open_point_factor
      R f localization S p);

// The selected factor triangle gives equality of the whole underlying maps.
symbol affine_spec_basic_open_point_lift_triangle
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S))
  : τ (@=
      (@CommRingHom R S)
      (@comm_ring_hom_comp_pointwise
        R
        (@comm_ring_localization_target R f localization)
        S
        (@affine_spec_basic_open_point_lift
          R f localization S p)
        (@comm_ring_localization_map R f localization))
      (@affine_spec_basic_open_point_map R f S p))
≔ @comm_ring_hom_ext
    R S
    (@comm_ring_hom_comp_pointwise
      R
      (@comm_ring_localization_target R f localization)
      S
      (@affine_spec_basic_open_point_lift
        R f localization S p)
      (@comm_ring_localization_map R f localization))
    (@affine_spec_basic_open_point_map R f S p)
    (@comm_ring_localization_factor_agreement
      R
      (@comm_ring_localization_target R f localization)
      S
      (@comm_ring_localization_map R f localization)
      (@affine_spec_basic_open_point_map R f S p)
      (@affine_spec_basic_open_point_factor
        R f localization S p));

// Unit evidence is proposition-valued, also along a path of structured maps.
protected symbol affine_spec_basic_open_unit_pathover
  [R S : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  [h k : τ (@CommRingHom R S)]
  (p : τ (@= (@CommRingHom R S) h k))
  (u : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h f)))
  (v : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S k f)))
  : τ (@PathOver
      (@CommRingHom R S)
      (λ q : τ (@CommRingHom R S),
        @CommRingUnitEvidence S (@comm_ring_hom_apply R S q f))
      h k p u v)
≔ @ind_eqr
    (@CommRingHom R S)
    k
    (λ h0 : τ (@CommRingHom R S),
      λ p0 : τ (@= (@CommRingHom R S) h0 k),
        @Pi_grpd
          (@CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h0 f))
          (λ u0 : τ (@CommRingUnitEvidence S
              (@comm_ring_hom_apply R S h0 f)),
            @Pi_grpd
              (@CommRingUnitEvidence S
                (@comm_ring_hom_apply R S k f))
              (λ v0 : τ (@CommRingUnitEvidence S
                  (@comm_ring_hom_apply R S k f)),
                @PathOver
                  (@CommRingHom R S)
                  (λ q : τ (@CommRingHom R S),
                    @CommRingUnitEvidence S
                      (@comm_ring_hom_apply R S q f))
                  h0 k p0 u0 v0)))
    (λ u0 : τ (@CommRingUnitEvidence S
        (@comm_ring_hom_apply R S k f)),
      λ v0 : τ (@CommRingUnitEvidence S
          (@comm_ring_hom_apply R S k f)),
        @is_contr_center
          (@= (@CommRingUnitEvidence S
              (@comm_ring_hom_apply R S k f)) u0 v0)
          ((@comm_ring_unit_evidence_is_prop
              S (@comm_ring_hom_apply R S k f)) u0 v0))
    h p u v;

// The point reconstructed from its selected factor equals the original point.
symbol affine_spec_basic_open_point_right_law
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (p : τ (@AffineSpecBasicOpenPoint R f S))
  : τ (@=
      (@AffineSpecBasicOpenPoint R f S)
      (@affine_spec_basic_open_point_from_localized_map
        R f localization S
        (@affine_spec_basic_open_point_lift
          R f localization S p))
      p)
≔ @Struct_sigma
    (@= (@CommRingHom R S)
      (@comm_ring_hom_comp_pointwise
        R
        (@comm_ring_localization_target R f localization)
        S
        (@affine_spec_basic_open_point_lift
          R f localization S p)
        (@comm_ring_localization_map R f localization))
      (@affine_spec_basic_open_point_map R f S p))
    (λ q : τ (@= (@CommRingHom R S)
        (@comm_ring_hom_comp_pointwise
          R
          (@comm_ring_localization_target R f localization)
          S
          (@affine_spec_basic_open_point_lift
            R f localization S p)
          (@comm_ring_localization_map R f localization))
        (@affine_spec_basic_open_point_map R f S p)),
      @PathOver
        (@CommRingHom R S)
        (λ h : τ (@CommRingHom R S),
          @CommRingUnitEvidence S (@comm_ring_hom_apply R S h f))
        (@comm_ring_hom_comp_pointwise
          R
          (@comm_ring_localization_target R f localization)
          S
          (@affine_spec_basic_open_point_lift
            R f localization S p)
          (@comm_ring_localization_map R f localization))
        (@affine_spec_basic_open_point_map R f S p)
        q
        (sigma_Snd
          (@affine_spec_basic_open_point_from_localized_map
            R f localization S
            (@affine_spec_basic_open_point_lift
              R f localization S p)))
        (@affine_spec_basic_open_point_unit R f S p))
    (@affine_spec_basic_open_point_lift_triangle
      R f localization S p)
    (@affine_spec_basic_open_unit_pathover
      R S f
      (@comm_ring_hom_comp_pointwise
        R
        (@comm_ring_localization_target R f localization)
        S
        (@affine_spec_basic_open_point_lift
          R f localization S p)
        (@comm_ring_localization_map R f localization))
      (@affine_spec_basic_open_point_map R f S p)
      (@affine_spec_basic_open_point_lift_triangle
        R f localization S p)
      (sigma_Snd
        (@affine_spec_basic_open_point_from_localized_map
          R f localization S
          (@affine_spec_basic_open_point_lift
            R f localization S p)))
      (@affine_spec_basic_open_point_unit R f S p));

// A supplied map k is a competing factor for the point obtained from k.
symbol affine_spec_basic_open_map_competitor
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R f localization)
      S
      (@comm_ring_localization_map R f localization)
      (@affine_spec_basic_open_point_map
        R f S
        (@affine_spec_basic_open_point_from_localized_map
          R f localization S k)))
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_localization_target R f localization)
    S
    (@comm_ring_localization_map R f localization)
    (@affine_spec_basic_open_point_map
      R f S
      (@affine_spec_basic_open_point_from_localized_map
        R f localization S k))
    k
    (λ x : τ (@comm_ring_carrier R),
      @eq_refl
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply
          (@comm_ring_localization_target R f localization)
          S k
          (@comm_ring_hom_apply
            R
            (@comm_ring_localization_target R f localization)
            (@comm_ring_localization_map R f localization)
            x)));

// Contractibility identifies the selected lift with the supplied map k.
symbol affine_spec_basic_open_point_left_law
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  [S : τ CommRing]
  (k : τ (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S))
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (@affine_spec_basic_open_point_lift
        R f localization S
        (@affine_spec_basic_open_point_from_localized_map
          R f localization S k))
      k)
≔ @eq_ap
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R f localization)
      S
      (@comm_ring_localization_map R f localization)
      (@affine_spec_basic_open_point_map
        R f S
        (@affine_spec_basic_open_point_from_localized_map
          R f localization S k)))
    (@CommRingHom
      (@comm_ring_localization_target R f localization)
      S)
    (λ factor : τ (@CommRingLocalizationFactor
        R
        (@comm_ring_localization_target R f localization)
        S
        (@comm_ring_localization_map R f localization)
        (@affine_spec_basic_open_point_map
          R f S
          (@affine_spec_basic_open_point_from_localized_map
            R f localization S k))),
      @comm_ring_localization_factor_map
        R
        (@comm_ring_localization_target R f localization)
        S
        (@comm_ring_localization_map R f localization)
        (@affine_spec_basic_open_point_map
          R f S
          (@affine_spec_basic_open_point_from_localized_map
            R f localization S k))
        factor)
    (@affine_spec_basic_open_point_factor
      R f localization S
      (@affine_spec_basic_open_point_from_localized_map
        R f localization S k))
    (@affine_spec_basic_open_map_competitor
      R f localization S k)
    (@is_contr_path
      (@CommRingLocalizationFactor
        R
        (@comm_ring_localization_target R f localization)
        S
        (@comm_ring_localization_map R f localization)
        (@affine_spec_basic_open_point_map
          R f S
          (@affine_spec_basic_open_point_from_localized_map
            R f localization S k)))
      (@comm_ring_localization_factorization_is_contr
        R f
        (@comm_ring_localization_target R f localization)
        (@comm_ring_localization_map R f localization)
        (@comm_ring_localization_property R f localization)
        S
        (@affine_spec_basic_open_point_map
          R f S
          (@affine_spec_basic_open_point_from_localized_map
            R f localization S k))
        (@affine_spec_basic_open_point_unit
          R f S
          (@affine_spec_basic_open_point_from_localized_map
            R f localization S k)))
      (@affine_spec_basic_open_map_competitor
        R f localization S k));

symbol affine_spec_basic_open_point_equiv_by_inverse
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  (S : τ CommRing)
  : τ (@EquivByInverse
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (@AffineSpecBasicOpenPoint R f S)
      (λ k : τ (@CommRingHom
          (@comm_ring_localization_target R f localization)
          S),
        @affine_spec_basic_open_point_from_localized_map
          R f localization S k)
      (λ p : τ (@AffineSpecBasicOpenPoint R f S),
        @affine_spec_basic_open_point_lift
          R f localization S p))
≔ @Product_pair_grpd
    (@Pi_grpd
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (λ k : τ (@CommRingHom
          (@comm_ring_localization_target R f localization)
          S),
        @=
          (@CommRingHom
            (@comm_ring_localization_target R f localization)
            S)
          (@affine_spec_basic_open_point_lift
            R f localization S
            (@affine_spec_basic_open_point_from_localized_map
              R f localization S k))
          k))
    (@Pi_grpd
      (@AffineSpecBasicOpenPoint R f S)
      (λ p : τ (@AffineSpecBasicOpenPoint R f S),
        @=
          (@AffineSpecBasicOpenPoint R f S)
          (@affine_spec_basic_open_point_from_localized_map
            R f localization S
            (@affine_spec_basic_open_point_lift
              R f localization S p))
          p))
    (λ k : τ (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S),
      @affine_spec_basic_open_point_left_law
        R f localization S k)
    (λ p : τ (@AffineSpecBasicOpenPoint R f S),
      @affine_spec_basic_open_point_right_law
        R f localization S p);

symbol affine_spec_basic_open_point_type_equiv
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  (S : τ CommRing)
  : τ (TypeEquiv
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (@AffineSpecBasicOpenPoint R f S))
≔ @Struct_sigma
    (@Function_grpd
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (@AffineSpecBasicOpenPoint R f S))
    (λ forward : τ (@Function_grpd
        (@CommRingHom
          (@comm_ring_localization_target R f localization)
          S)
        (@AffineSpecBasicOpenPoint R f S)),
      @IsEquivMap
        (@CommRingHom
          (@comm_ring_localization_target R f localization)
          S)
        (@AffineSpecBasicOpenPoint R f S)
        forward)
    (λ k : τ (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S),
      @affine_spec_basic_open_point_from_localized_map
        R f localization S k)
    (@is_equiv_map_by_inverse
      (@CommRingHom
        (@comm_ring_localization_target R f localization)
        S)
      (@AffineSpecBasicOpenPoint R f S)
      (λ k : τ (@CommRingHom
          (@comm_ring_localization_target R f localization)
          S),
        @affine_spec_basic_open_point_from_localized_map
          R f localization S k)
      (λ p : τ (@AffineSpecBasicOpenPoint R f S),
        @affine_spec_basic_open_point_lift
          R f localization S p)
      (@affine_spec_basic_open_point_equiv_by_inverse
        R f localization S));
