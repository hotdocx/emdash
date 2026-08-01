/*
  Presented finite basic-open Zariski covers and elementwise base change.

  This rule-free one-way module combines an algebraic unimodular cover
  presentation with selected universal-property localization packages.  For
  one generator it derives the base-change factor, its pointwise triangle, the
  corresponding arrow in the affine restriction total, and actual membership
  in the pulled-back ordinary sieve.

  These are inspectable computational presentation data.  The module declares
  no global choice of localizations, propositional truncation, generated
  coverage, Grothendieck topology, subcanonicity, sheafhood, Spec, or scheme.
*/

require open emdash.emdash3_2_commutative_algebra_finite;
require open emdash.emdash3_2_commutative_algebra_localization;
require open emdash.emdash3_2_sites;

/*
  Selected localization packages over a finite generator family.

  The dependent finite fold preserves the correspondence between each
  generator f_i and its selected `CommRingLocalizationAt(R,f_i)` package.
*/
symbol CommRingLocalizationFamily
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (generators : τ (@FiniteFamily (@comm_ring_carrier R) n))
  : Grpd
≔ @FiniteFamilyAll
    (@comm_ring_carrier R)
    (λ f : τ (@comm_ring_carrier R),
      @CommRingLocalizationAt R f)
    n generators;

symbol comm_ring_localization_family_nil
  (R : τ CommRing)
  : τ (@CommRingLocalizationFamily
      R zero (@finite_family_nil (@comm_ring_carrier R)))
≔ @finite_family_all_nil
    (@comm_ring_carrier R)
    (λ f : τ (@comm_ring_carrier R),
      @CommRingLocalizationAt R f);

symbol comm_ring_localization_family_cons
  [R : τ CommRing]
  [n : τ Nat_grpd]
  [f : τ (@comm_ring_carrier R)]
  [generators : τ (@FiniteFamily (@comm_ring_carrier R) n)]
  (localization : τ (@CommRingLocalizationAt R f))
  (tail : τ (@CommRingLocalizationFamily R n generators))
  : τ (@CommRingLocalizationFamily
      R
      (succ n)
      (@finite_family_cons
        (@comm_ring_carrier R) n f generators))
≔ @finite_family_all_cons
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @CommRingLocalizationAt R x)
    n f generators
    localization tail;

symbol comm_ring_localization_family_head
  [R : τ CommRing]
  [n : τ Nat_grpd]
  [generators : τ (@FiniteFamily
      (@comm_ring_carrier R) (succ n))]
  (localizations : τ (@CommRingLocalizationFamily
      R (succ n) generators))
  : τ (@CommRingLocalizationAt
      R
      (@finite_family_head (@comm_ring_carrier R) n generators))
≔ @finite_family_all_head
    (@comm_ring_carrier R)
    (λ f : τ (@comm_ring_carrier R),
      @CommRingLocalizationAt R f)
    n generators localizations;

symbol comm_ring_localization_family_tail
  [R : τ CommRing]
  [n : τ Nat_grpd]
  [generators : τ (@FiniteFamily
      (@comm_ring_carrier R) (succ n))]
  (localizations : τ (@CommRingLocalizationFamily
      R (succ n) generators))
  : τ (@CommRingLocalizationFamily
      R n
      (@finite_family_tail (@comm_ring_carrier R) n generators))
≔ @finite_family_all_tail
    (@comm_ring_carrier R)
    (λ f : τ (@comm_ring_carrier R),
      @CommRingLocalizationAt R f)
    n generators localizations;

symbol comm_ring_localization_family_singleton
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  : τ (@CommRingLocalizationFamily
      R
      (succ zero)
      (@finite_family_singleton (@comm_ring_carrier R) f))
≔ @comm_ring_localization_family_cons
    R zero f
    (@finite_family_nil (@comm_ring_carrier R))
    localization
    (@comm_ring_localization_family_nil R);

/*
  A presented finite Zariski cover retains both the algebraic unit-ideal data
  and selected localization packages.  It is presentation data, not a mere
  proposition and not yet a sieve coverage.
*/
symbol CommRingZariskiCoverFamily
  (R : τ CommRing)
  : Grpd
≔ `Σ_ cover : τ (@CommRingZariskiCoverPresentation R),
    @CommRingLocalizationFamily
      R
      (@comm_ring_zariski_cover_length R cover)
      (@comm_ring_zariski_cover_generators R cover);

symbol comm_ring_zariski_cover_family_intro
  [R : τ CommRing]
  (cover : τ (@CommRingZariskiCoverPresentation R))
  (localizations : τ (@CommRingLocalizationFamily
      R
      (@comm_ring_zariski_cover_length R cover)
      (@comm_ring_zariski_cover_generators R cover)))
  : τ (@CommRingZariskiCoverFamily R)
≔ @Struct_sigma
    (@CommRingZariskiCoverPresentation R)
    (λ c : τ (@CommRingZariskiCoverPresentation R),
      @CommRingLocalizationFamily
        R
        (@comm_ring_zariski_cover_length R c)
        (@comm_ring_zariski_cover_generators R c))
    cover localizations;

symbol comm_ring_zariski_cover_family_presentation
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  : τ (@CommRingZariskiCoverPresentation R)
≔ sigma_Fst family;

symbol comm_ring_zariski_cover_family_length
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  : τ Nat_grpd
≔ @comm_ring_zariski_cover_length
    R (@comm_ring_zariski_cover_family_presentation R family);

symbol comm_ring_zariski_cover_family_generators
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  : τ (@FiniteFamily
      (@comm_ring_carrier R)
      (@comm_ring_zariski_cover_family_length R family))
≔ @comm_ring_zariski_cover_generators
    R (@comm_ring_zariski_cover_family_presentation R family);

symbol comm_ring_zariski_cover_family_unimodular
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  : τ (@CommRingUnimodularPresentation
      R
      (@comm_ring_zariski_cover_family_length R family)
      (@comm_ring_zariski_cover_family_generators R family))
≔ @comm_ring_zariski_cover_unimodular
    R (@comm_ring_zariski_cover_family_presentation R family);

symbol comm_ring_zariski_cover_family_localizations
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  : τ (@CommRingLocalizationFamily
      R
      (@comm_ring_zariski_cover_family_length R family)
      (@comm_ring_zariski_cover_family_generators R family))
≔ sigma_Snd family;

// The nonempty singleton cover accepts, rather than globally chooses, Loc_R(1).
symbol comm_ring_unit_zariski_cover_family
  (R : τ CommRing)
  (localization : τ (@CommRingLocalizationAt R (@comm_ring_one R)))
  : τ (@CommRingZariskiCoverFamily R)
≔ @comm_ring_zariski_cover_family_intro
    R
    (@comm_ring_unit_zariski_cover R)
    (@comm_ring_localization_family_singleton
      R (@comm_ring_one R) localization);

/*
  Two theorem-level affine variance comparisons.

  The first path is used by the Sigma-arrow triangle: opposite-category
  precomposition meets ordinary ring postcomposition, then generic and
  pointwise ring composition.  The second path compares the selected
  pointwise composite with the canonical restriction-total postcomposition
  object.  Neither path changes runtime normal forms.
*/
symbol comm_ring_affine_op_precomp_pointwise_path
  [R L T : τ CommRing]
  (factor : τ (@CommRingHom L T))
  (localization_map : τ (@CommRingHom R L))
  : τ (@=
      (@CommRingHom R T)
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        R T L factor localization_map)
      (@comm_ring_hom_comp_pointwise R L T factor localization_map))
≔ @eq_trans
    (@CommRingHom R T)
    (@hom_precomp_along_fapp0
      (Op_cat CommRing_cat)
      (Op_cat CommRing_cat)
      (@id_func (Op_cat CommRing_cat))
      R T L factor localization_map)
    (@hom_postcomp_fapp0
      CommRing_cat
      CommRing_cat
      (@id_func CommRing_cat)
      R L T factor localization_map)
    (@comm_ring_hom_comp_pointwise R L T factor localization_map)
    (@eq_refl
      (@CommRingHom R T)
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        R T L factor localization_map))
    (@eq_trans
      (@CommRingHom R T)
      (@hom_postcomp_fapp0
        CommRing_cat
        CommRing_cat
        (@id_func CommRing_cat)
        R L T factor localization_map)
      (@comm_ring_hom_comp R L T factor localization_map)
      (@comm_ring_hom_comp_pointwise R L T factor localization_map)
      (@eq_refl
        (@CommRingHom R T)
        (@hom_postcomp_fapp0
          CommRing_cat
          CommRing_cat
          (@id_func CommRing_cat)
          R L T factor localization_map))
      (@comm_ring_hom_comp_pointwise_path
        R L T factor localization_map));

symbol comm_ring_affine_pointwise_postcomp_path
  [R S T : τ CommRing]
  (h : τ (@CommRingHom R S))
  (g : τ (@CommRingHom S T))
  : τ (@=
      (@CommRingHom R T)
      (@comm_ring_hom_comp_pointwise R S T g h)
      (@hom_postcomp_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        T S R h g))
≔ @eq_trans
    (@CommRingHom R T)
    (@comm_ring_hom_comp_pointwise R S T g h)
    (@hom_precomp_along_fapp0
      CommRing_cat
      CommRing_cat
      (@id_func CommRing_cat)
      T R S h g)
    (@hom_postcomp_fapp0
      (Op_cat CommRing_cat)
      (Op_cat CommRing_cat)
      (@id_func (Op_cat CommRing_cat))
      T S R h g)
    (@eq_sym
      (@CommRingHom R T)
      (@hom_precomp_along_fapp0
        CommRing_cat
        CommRing_cat
        (@id_func CommRing_cat)
        T R S h g)
      (@comm_ring_hom_comp_pointwise R S T g h)
      (@eq_trans
        (@CommRingHom R T)
        (@hom_precomp_along_fapp0
          CommRing_cat
          CommRing_cat
          (@id_func CommRing_cat)
          T R S h g)
        (@comm_ring_hom_comp R S T g h)
        (@comm_ring_hom_comp_pointwise R S T g h)
        (@eq_refl
          (@CommRingHom R T)
          (@hom_precomp_along_fapp0
            CommRing_cat
            CommRing_cat
            (@id_func CommRing_cat)
            T R S h g))
        (@comm_ring_hom_comp_pointwise_path R S T g h)))
    (@eq_sym
      (@CommRingHom R T)
      (@hom_postcomp_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        T S R h g)
      (@hom_precomp_along_fapp0
        CommRing_cat
        CommRing_cat
        (@id_func CommRing_cat)
        T R S h g)
      (@eq_refl
        (@CommRingHom R T)
        (@hom_postcomp_fapp0
          (Op_cat CommRing_cat)
          (Op_cat CommRing_cat)
          (@id_func (Op_cat CommRing_cat))
          T S R h g)));

/*
  A chosen localization is the affine basic-open arrow into its source ring.
  For K = Op(CommRing_cat), a ring map R -> L is an arrow L -> R in K.
*/
symbol comm_ring_basic_open_arrow
  [R : τ CommRing]
  [f : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R f))
  : τ (Obj (@Into_restr_cat (Op_cat CommRing_cat) R))
≔ Struct_sigma
    (@comm_ring_localization_target R f localization)
    (@comm_ring_localization_map R f localization);

/*
  Elementwise base change of a chosen basic open.

  For h : R -> S and selected localizations at f and h(f), the target
  localization map after h inverts f.  The universal property of the source
  localization supplies the comparison factor and its pointwise triangle.
*/
symbol comm_ring_basic_open_base_change_composite
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  : τ (@CommRingHom
      R
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization))
≔ @comm_ring_hom_comp_pointwise
    R S
    (@comm_ring_localization_target
      S (@comm_ring_hom_apply R S h f) target_localization)
    (@comm_ring_localization_map
      S (@comm_ring_hom_apply R S h f) target_localization)
    h;

symbol comm_ring_basic_open_base_change_factor
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_localization_map R f source_localization)
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization))
≔ @is_contr_center
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_localization_map R f source_localization)
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization))
    (@comm_ring_localization_factorization_is_contr
      R f
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_map R f source_localization)
      (@comm_ring_localization_property R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization)
      (@comm_ring_localization_inverted_unit
        S
        (@comm_ring_hom_apply R S h f)
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_localization_map
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_localization_property
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)));

symbol comm_ring_basic_open_base_change_factor_map
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  : τ (@CommRingHom
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization))
≔ @comm_ring_localization_factor_map
    R
    (@comm_ring_localization_target R f source_localization)
    (@comm_ring_localization_target
      S
      (@comm_ring_hom_apply R S h f)
      target_localization)
    (@comm_ring_localization_map R f source_localization)
    (@comm_ring_basic_open_base_change_composite
      R S h f target_localization)
    (@comm_ring_basic_open_base_change_factor
      R S h f source_localization target_localization);

// Universal-factor agreement upgraded from carrier points to a whole map path.
symbol comm_ring_basic_open_base_change_factor_pointwise_path
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  : τ (@=
      (@CommRingHom
        R
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization))
      (@comm_ring_hom_comp_pointwise
        R
        (@comm_ring_localization_target R f source_localization)
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_factor_map
          R S h f source_localization target_localization)
        (@comm_ring_localization_map R f source_localization))
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization))
≔ @comm_ring_hom_ext
    R
    (@comm_ring_localization_target
      S
      (@comm_ring_hom_apply R S h f)
      target_localization)
    (@comm_ring_hom_comp_pointwise
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_basic_open_base_change_factor_map
        R S h f source_localization target_localization)
      (@comm_ring_localization_map R f source_localization))
    (@comm_ring_basic_open_base_change_composite
      R S h f target_localization)
    (@comm_ring_localization_factor_agreement
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_localization_map R f source_localization)
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization)
      (@comm_ring_basic_open_base_change_factor
        R S h f source_localization target_localization));

// The same triangle with generic ring-category composition on its left.
symbol comm_ring_basic_open_base_change_triangle
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  : τ (@=
      (@CommRingHom
        R
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization))
      (@comm_ring_hom_comp
        R
        (@comm_ring_localization_target R f source_localization)
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_factor_map
          R S h f source_localization target_localization)
        (@comm_ring_localization_map R f source_localization))
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization))
≔ @eq_trans
    (@CommRingHom
      R
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization))
    (@comm_ring_hom_comp
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_basic_open_base_change_factor_map
        R S h f source_localization target_localization)
      (@comm_ring_localization_map R f source_localization))
    (@comm_ring_hom_comp_pointwise
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_basic_open_base_change_factor_map
        R S h f source_localization target_localization)
      (@comm_ring_localization_map R f source_localization))
    (@comm_ring_basic_open_base_change_composite
      R S h f target_localization)
    (@comm_ring_hom_comp_pointwise_path
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_basic_open_base_change_factor_map
        R S h f source_localization target_localization)
      (@comm_ring_localization_map R f source_localization))
    (@comm_ring_basic_open_base_change_factor_pointwise_path
      R S h f source_localization target_localization);

// Triangle at the exact stable precomposition endpoint required by Sigma.
symbol comm_ring_basic_open_base_change_precomp_triangle
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  : τ (@=
      (@CommRingHom
        R
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization))
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id_func (Op_cat CommRing_cat))
        R
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_localization_target R f source_localization)
        (@comm_ring_basic_open_base_change_factor_map
          R S h f source_localization target_localization)
        (@comm_ring_localization_map R f source_localization))
      (@comm_ring_basic_open_base_change_composite
        R S h f target_localization))
≔ @eq_trans
    (@CommRingHom
      R
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization))
    (@hom_precomp_along_fapp0
      (Op_cat CommRing_cat)
      (Op_cat CommRing_cat)
      (@id_func (Op_cat CommRing_cat))
      R
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_basic_open_base_change_factor_map
        R S h f source_localization target_localization)
      (@comm_ring_localization_map R f source_localization))
    (@comm_ring_hom_comp_pointwise
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_basic_open_base_change_factor_map
        R S h f source_localization target_localization)
      (@comm_ring_localization_map R f source_localization))
    (@comm_ring_basic_open_base_change_composite
      R S h f target_localization)
    (@comm_ring_affine_op_precomp_pointwise_path
      R
      (@comm_ring_localization_target R f source_localization)
      (@comm_ring_localization_target
        S
        (@comm_ring_hom_apply R S h f)
        target_localization)
      (@comm_ring_basic_open_base_change_factor_map
        R S h f source_localization target_localization)
      (@comm_ring_localization_map R f source_localization))
    (@comm_ring_basic_open_base_change_factor_pointwise_path
      R S h f source_localization target_localization);

// The factor and stable triangle form the restriction-total base-change arrow.
symbol comm_ring_basic_open_base_change_into_arrow
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  : τ (Hom
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@comm_ring_basic_open_arrow R f source_localization)
      (@Struct_sigma
        (Obj CommRing_cat)
        (λ T : τ (Obj CommRing_cat),
          Obj (@Fibre_cat
            CommRing_cat
            (@yoneda_psh (Op_cat CommRing_cat) R)
            T))
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization)))
≔ @sigma_arrow
    CommRing_cat
    (@yoneda_psh (Op_cat CommRing_cat) R)
    (@comm_ring_localization_target R f source_localization)
    (@comm_ring_localization_target
      S
      (@comm_ring_hom_apply R S h f)
      target_localization)
    (@comm_ring_localization_map R f source_localization)
    (@comm_ring_basic_open_base_change_composite
      R S h f target_localization)
    (@comm_ring_basic_open_base_change_factor_map
      R S h f source_localization target_localization)
    (@comm_ring_basic_open_base_change_precomp_triangle
      R S h f source_localization target_localization);

/*
  Sieve membership is transported first along the universal-property Sigma
  arrow, then to the canonical postcomposition object, and finally observed in
  the ordinary sieve pullback.  Each step returns an actual term.
*/
symbol comm_ring_basic_open_membership_at_composite
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@comm_ring_basic_open_arrow R f source_localization)))
  : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@Struct_sigma
        (Obj CommRing_cat)
        (λ T : τ (Obj CommRing_cat),
          Obj (@Fibre_cat
            CommRing_cat
            (@yoneda_psh (Op_cat CommRing_cat) R)
            T))
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization)))
≔ @fapp0
    (@Fibre_cat
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@sieve_higher (Op_cat CommRing_cat) R Q)
      (@comm_ring_basic_open_arrow R f source_localization))
    (@Fibre_cat
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@sieve_higher (Op_cat CommRing_cat) R Q)
      (@Struct_sigma
        (Obj CommRing_cat)
        (λ T : τ (Obj CommRing_cat),
          Obj (@Fibre_cat
            CommRing_cat
            (@yoneda_psh (Op_cat CommRing_cat) R)
            T))
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization)))
    (@catd_transport_func
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@sieve_higher (Op_cat CommRing_cat) R Q)
      (@comm_ring_basic_open_arrow R f source_localization)
      (@Struct_sigma
        (Obj CommRing_cat)
        (λ T : τ (Obj CommRing_cat),
          Obj (@Fibre_cat
            CommRing_cat
            (@yoneda_psh (Op_cat CommRing_cat) R)
            T))
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization))
      (@comm_ring_basic_open_base_change_into_arrow
        R S h f source_localization target_localization))
    member;

symbol comm_ring_basic_open_membership_at_postcompose
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@comm_ring_basic_open_arrow R f source_localization)))
  : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@into_restr_postcompose
        (Op_cat CommRing_cat)
        S R h
        (@comm_ring_basic_open_arrow
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)))
≔ @fapp0
    (@Fibre_cat
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@sieve_higher (Op_cat CommRing_cat) R Q)
      (@Struct_sigma
        (Obj CommRing_cat)
        (λ T : τ (Obj CommRing_cat),
          Obj (@Fibre_cat
            CommRing_cat
            (@yoneda_psh (Op_cat CommRing_cat) R)
            T))
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization)))
    (@Fibre_cat
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@sieve_higher (Op_cat CommRing_cat) R Q)
      (@into_restr_postcompose
        (Op_cat CommRing_cat)
        S R h
        (@comm_ring_basic_open_arrow
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)))
    (@catd_transport_func
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (@sieve_higher (Op_cat CommRing_cat) R Q)
      (@Struct_sigma
        (Obj CommRing_cat)
        (λ T : τ (Obj CommRing_cat),
          Obj (@Fibre_cat
            CommRing_cat
            (@yoneda_psh (Op_cat CommRing_cat) R)
            T))
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization))
      (@into_restr_postcompose
        (Op_cat CommRing_cat)
        S R h
        (@comm_ring_basic_open_arrow
          S
          (@comm_ring_hom_apply R S h f)
          target_localization))
      (@into_restr_postcompose_constructor_arrow
        (Op_cat CommRing_cat)
        (@comm_ring_localization_target
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        S R
        h
        (@comm_ring_localization_map
          S
          (@comm_ring_hom_apply R S h f)
          target_localization)
        (@comm_ring_basic_open_base_change_composite
          R S h f target_localization)
        (@comm_ring_affine_pointwise_postcomp_path
          R S
          (@comm_ring_localization_target
            S
            (@comm_ring_hom_apply R S h f)
            target_localization)
          h
          (@comm_ring_localization_map
            S
            (@comm_ring_hom_apply R S h f)
            target_localization))))
    (@comm_ring_basic_open_membership_at_composite
      R S h f source_localization target_localization Q member);

// Elementwise pullback stability for a chosen localization-generated arrow.
symbol comm_ring_basic_open_pullback_membership
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier R)]
  (source_localization : τ (@CommRingLocalizationAt R f))
  (target_localization : τ (@CommRingLocalizationAt
      S (@comm_ring_hom_apply R S h f)))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R Q
      (@comm_ring_basic_open_arrow R f source_localization)))
  : τ (@SieveMembership
      (Op_cat CommRing_cat)
      S
      (@sieve_pullback
        (Op_cat CommRing_cat)
        S R h Q)
      (@comm_ring_basic_open_arrow
        S
        (@comm_ring_hom_apply R S h f)
        target_localization))
≔ @sieve_pullback_membership
    (Op_cat CommRing_cat)
    S R h Q
    (@comm_ring_basic_open_arrow
      S
      (@comm_ring_hom_apply R S h f)
      target_localization)
    (@comm_ring_basic_open_membership_at_postcompose
      R S h f source_localization target_localization Q member);
