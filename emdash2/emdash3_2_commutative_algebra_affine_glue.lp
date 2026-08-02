/*
  Computational affine Cartier glue for the identity structure presheaf.

  On K = CommRing_cat^op, the identity functor on CommRing_cat is a
  CommRing-valued presheaf.  Given a selected localization i:R->L at s, the
  literal support element (L,i,i(s)^-1) is a canonical centre of D(s).
  Evaluation of an internally coherent matching section at that centre is a
  genuine glue functor.

  Contractibility of localization factors identifies the centre factor with
  id_L, giving glue(restrict(x))=x.  For every other support member h:R->V,
  its selected universal factor k:L->V and factor triangle give an arrow from
  the centre to that member.  Generic Pi-section action along this arrow gives
  k(glue(m))=m(V,h) internally.  Sigma elimination extends the literal-member
  equation to every encoded support element.

  The module adds no rewrite or unification rules and no external naturality
  fields.  It constructs the existing selected `CommRingPshLocalizationGlue`
  package for every chosen affine localization.  That package retains
  point/component inverse laws; this file does not claim equality of whole
  functors, `OmegaEquivAlong Cat_cat`, ordinary covering-sieve descent,
  sheafhood, a generated topology, `Spec`, or a scheme.
*/

require open emdash.emdash3_2_commutative_algebra_glue;

// The affine CommRing-valued presheaf on CommRing_cat^op is identity.
symbol affine_comm_ring_psh
  : τ (@CommRingPsh (Op_cat CommRing_cat))
≔ @id_func CommRing_cat;

// The localization map sends s to a unit and therefore lies in D(s).
symbol affine_localization_support_member
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R
      (@comm_ring_psh_invertibility_sieve
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Struct_sigma
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_map R s localization)))
≔ @comm_ring_localization_inverted_unit
    R s
    (@comm_ring_localization_target R s localization)
    (@comm_ring_localization_map R s localization)
    (@comm_ring_localization_property R s localization);

// Canonical centre (L,i,unit evidence) of the support-elements category.
symbol affine_localization_support_center
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (Obj (@CommRingPshInvertibilityElements_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s))
≔ @comm_ring_psh_invertibility_element
    (Op_cat CommRing_cat)
    affine_comm_ring_psh
    R s
    (@comm_ring_localization_target R s localization)
    (@comm_ring_localization_map R s localization)
    (@affine_localization_support_member R s localization);

// Cartier glue evaluates an internally coherent matching section at centre.
symbol affine_localization_matching_glue_func
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (Functor
      (@CommRingPshLocalizationMatching_cat
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Path_cat (@comm_ring_carrier
        (@comm_ring_localization_target R s localization))))
≔ @piapp0_func
    (@CommRingPshInvertibilityElements_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)
    (@comm_ring_psh_localization_matching_catd
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)
    (@affine_localization_support_center R s localization);

// The identity structured map is a competing factor of i:R->L through i.
symbol affine_localization_identity_factor
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_map R s localization)
      (@comm_ring_localization_map R s localization))
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_localization_target R s localization)
    (@comm_ring_localization_target R s localization)
    (@comm_ring_localization_map R s localization)
    (@comm_ring_localization_map R s localization)
    (@comm_ring_hom_id_pointwise
      (@comm_ring_localization_target R s localization))
    (λ x : τ (@comm_ring_carrier R),
      @eq_refl
        (@comm_ring_carrier
          (@comm_ring_localization_target R s localization))
        (@comm_ring_hom_apply
          R
          (@comm_ring_localization_target R s localization)
          (@comm_ring_localization_map R s localization)
          x));

// Contractibility identifies the universally selected centre factor with id.
symbol affine_localization_center_factor_package_path
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (@=
      (@CommRingLocalizationFactor
        R
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_map R s localization)
        (@comm_ring_localization_map R s localization))
      (@comm_ring_psh_localization_factor_at_member
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s localization
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_map R s localization)
        (@affine_localization_support_member R s localization))
      (@affine_localization_identity_factor R s localization))
≔ @is_contr_path
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_map R s localization)
      (@comm_ring_localization_map R s localization))
    (@comm_ring_localization_factorization_is_contr
      R s
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_map R s localization)
      (@comm_ring_localization_property R s localization)
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_map R s localization)
      (@affine_localization_support_member R s localization))
    (@affine_localization_identity_factor R s localization);

// Project factor-package uniqueness to equality of whole structured maps.
symbol affine_localization_center_factor_map_path
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_target R s localization))
      (@comm_ring_psh_localization_factor_map_at_member
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s localization
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_map R s localization)
        (@affine_localization_support_member R s localization))
      (@comm_ring_hom_id_pointwise
        (@comm_ring_localization_target R s localization)))
≔ @eq_ap
    (@CommRingLocalizationFactor
      R
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_map R s localization)
      (@comm_ring_localization_map R s localization))
    (@CommRingHom
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_target R s localization))
    (λ factor : τ (@CommRingLocalizationFactor
        R
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_map R s localization)
        (@comm_ring_localization_map R s localization)),
      @comm_ring_localization_factor_map
        R
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_map R s localization)
        (@comm_ring_localization_map R s localization)
        factor)
    _ _
    (@affine_localization_center_factor_package_path R s localization);

// Evaluating restriction at the centre applies the selected centre factor.
symbol affine_localization_glue_restrict_path
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target R s localization)))
  : τ (@=
      (@comm_ring_carrier
        (@comm_ring_localization_target R s localization))
      (@fapp0
        (@CommRingPshLocalizationMatching_cat
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s)
        (Path_cat (@comm_ring_carrier
          (@comm_ring_localization_target R s localization)))
        (@affine_localization_matching_glue_func R s localization)
        (@comm_ring_psh_localization_matching_section
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s localization x))
      x)
≔ @eq_ap
    (@CommRingHom
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_target R s localization))
    (@comm_ring_carrier
      (@comm_ring_localization_target R s localization))
    (λ h : τ (@CommRingHom
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_target R s localization)),
      @comm_ring_hom_apply
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_target R s localization)
        h x)
    _ _
    (@affine_localization_center_factor_map_path R s localization);

// First component law of selected affine glue.
symbol affine_localization_glue_restrict_law
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (@CommRingPshLocalizationGlueRestrictLaw
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s localization
      (@affine_localization_matching_glue_func R s localization))
≔ λ x : τ (@comm_ring_carrier
      (@comm_ring_localization_target R s localization)),
    @affine_localization_glue_restrict_path R s localization x;

/*
  For every support member h:R->V, the universal factor k:L->V gives the
  canonical arrow from the localization centre (L,i) to (V,h).  First promote
  the pointwise factor agreement to equality of whole structured maps.
*/
symbol affine_localization_center_triangle_path
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (V : τ CommRing)
  (h : τ (@CommRingHom R V))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R
      (@comm_ring_psh_invertibility_sieve
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Struct_sigma V h)))
  : τ (@=
      (@CommRingHom R V)
      (@comm_ring_hom_comp_pointwise
        R
        (@comm_ring_localization_target R s localization)
        V
        (@comm_ring_psh_localization_factor_map_at_member
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s localization V h member)
        (@comm_ring_localization_map R s localization))
      h)
≔ @comm_ring_hom_ext
    R V
    (@comm_ring_hom_comp_pointwise
      R
      (@comm_ring_localization_target R s localization)
      V
      (@comm_ring_psh_localization_factor_map_at_member
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s localization V h member)
      (@comm_ring_localization_map R s localization))
    h
    (@comm_ring_localization_factor_agreement
      R
      (@comm_ring_localization_target R s localization)
      V
      (@comm_ring_localization_map R s localization)
      h
      (@comm_ring_psh_localization_factor_at_member
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s localization V h member));

/*
  The represented-presheaf transport head is intentionally staged through
  ordinary opposite composition and the selected pointwise structured-map
  comparison.  These are equality witnesses at proof time, not new runtime
  rules for Yoneda or structured-map composition.
*/
symbol affine_localization_center_transport_triangle_path
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (V : τ CommRing)
  (h : τ (@CommRingHom R V))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R
      (@comm_ring_psh_invertibility_sieve
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Struct_sigma V h)))
  : τ (@=
      (@CommRingHom R V)
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id Cat_cat (Op_cat CommRing_cat))
        R
        V
        (@comm_ring_localization_target R s localization)
        (@comm_ring_psh_localization_factor_map_at_member
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s localization V h member)
        (@comm_ring_localization_map R s localization))
      h)
≔ @eq_trans
    (@CommRingHom R V)
    (@hom_precomp_along_fapp0
      (Op_cat CommRing_cat)
      (Op_cat CommRing_cat)
      (@id Cat_cat (Op_cat CommRing_cat))
      R
      V
      (@comm_ring_localization_target R s localization)
      (@comm_ring_psh_localization_factor_map_at_member
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s localization V h member)
      (@comm_ring_localization_map R s localization))
    (@hom_postcomp_fapp0
      CommRing_cat
      CommRing_cat
      (@id Cat_cat CommRing_cat)
      R
      (@comm_ring_localization_target R s localization)
      V
      (@comm_ring_psh_localization_factor_map_at_member
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s localization V h member)
      (@comm_ring_localization_map R s localization))
    h
    (@eq_refl
      (@CommRingHom R V)
      (@hom_precomp_along_fapp0
        (Op_cat CommRing_cat)
        (Op_cat CommRing_cat)
        (@id Cat_cat (Op_cat CommRing_cat))
        R
        V
        (@comm_ring_localization_target R s localization)
        (@comm_ring_psh_localization_factor_map_at_member
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s localization V h member)
        (@comm_ring_localization_map R s localization)))
    (@eq_trans
      (@CommRingHom R V)
      (@hom_postcomp_fapp0
        CommRing_cat
        CommRing_cat
        (@id Cat_cat CommRing_cat)
        R
        (@comm_ring_localization_target R s localization)
        V
        (@comm_ring_psh_localization_factor_map_at_member
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s localization V h member)
        (@comm_ring_localization_map R s localization))
      (@comp_fapp0
        CommRing_cat
        R
        (@comm_ring_localization_target R s localization)
        V
        (@comm_ring_psh_localization_factor_map_at_member
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s localization V h member)
        (@comm_ring_localization_map R s localization))
      h
      (@eq_refl
        (@CommRingHom R V)
        (@hom_postcomp_fapp0
          CommRing_cat
          CommRing_cat
          (@id Cat_cat CommRing_cat)
          R
          (@comm_ring_localization_target R s localization)
          V
          (@comm_ring_psh_localization_factor_map_at_member
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s localization V h member)
          (@comm_ring_localization_map R s localization)))
      (@eq_trans
        (@CommRingHom R V)
        (@comp_fapp0
          CommRing_cat
          R
          (@comm_ring_localization_target R s localization)
          V
          (@comm_ring_psh_localization_factor_map_at_member
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s localization V h member)
          (@comm_ring_localization_map R s localization))
        (@comm_ring_hom_comp_pointwise
          R
          (@comm_ring_localization_target R s localization)
          V
          (@comm_ring_psh_localization_factor_map_at_member
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s localization V h member)
          (@comm_ring_localization_map R s localization))
        h
        (@comm_ring_hom_comp_pointwise_path
          R
          (@comm_ring_localization_target R s localization)
          V
          (@comm_ring_psh_localization_factor_map_at_member
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s localization V h member)
          (@comm_ring_localization_map R s localization))
        (@affine_localization_center_triangle_path
          R s localization V h member)));

// The universal factor and its triangle form an arrow in the restriction
// total from the localization centre to a literal support arrow.
symbol affine_localization_center_base_arrow
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (V : τ CommRing)
  (h : τ (@CommRingHom R V))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R
      (@comm_ring_psh_invertibility_sieve
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Struct_sigma V h)))
  : τ (Hom
      (@Into_restr_cat (Op_cat CommRing_cat) R)
      (Struct_sigma
        (@comm_ring_localization_target R s localization)
        (@comm_ring_localization_map R s localization))
      (Struct_sigma V h))
≔ @sigma_arrow
    CommRing_cat
    (@yoneda_psh (Op_cat CommRing_cat) R)
    (@comm_ring_localization_target R s localization)
    V
    (@comm_ring_localization_map R s localization)
    h
    (@comm_ring_psh_localization_factor_map_at_member
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s localization V h member)
    (@path_to_hom
      (@Fibre_cat
        CommRing_cat
        (@yoneda_psh (Op_cat CommRing_cat) R)
        V)
      _
      h
      (@affine_localization_center_transport_triangle_path
        R s localization V h member));

/*
  Lift the base arrow to the support-elements category.  The target sieve
  fibre is subterminal, so its retained proposition evidence selects the
  dependent arrow; no concrete proposition representation is inspected.
*/
symbol affine_localization_center_to_member_arrow
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (V : τ CommRing)
  (h : τ (@CommRingHom R V))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R
      (@comm_ring_psh_invertibility_sieve
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Struct_sigma V h)))
  : τ (Hom
      (@CommRingPshInvertibilityElements_cat
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (@affine_localization_support_center R s localization)
      (@comm_ring_psh_invertibility_element
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s V h member))
≔ @sigma_arrow
    (@Into_restr_cat (Op_cat CommRing_cat) R)
    (@sieve_higher
      (Op_cat CommRing_cat)
      R
      (@comm_ring_psh_invertibility_sieve
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s))
    (Struct_sigma
      (@comm_ring_localization_target R s localization)
      (@comm_ring_localization_map R s localization))
    (Struct_sigma V h)
    (@affine_localization_support_member R s localization)
    member
    (@affine_localization_center_base_arrow
      R s localization V h member)
    (@subterminal_cat_arrow
      (@Fibre_cat
        (@Into_restr_cat (Op_cat CommRing_cat) R)
        (@sieve_higher
          (Op_cat CommRing_cat)
          R
          (@comm_ring_psh_invertibility_sieve
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s))
        (Struct_sigma V h))
      ((@sieve_subterminal
          (Op_cat CommRing_cat)
          R
          (@comm_ring_psh_invertibility_sieve
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s))
        (Struct_sigma V h))
      _
      member);

// Pi-section action along the centre arrow is the literal Cartier equation.
symbol affine_localization_matching_cartier_path
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (matching : τ (Obj (@CommRingPshLocalizationMatching_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)))
  (V : τ CommRing)
  (h : τ (@CommRingHom R V))
  (member : τ (@SieveMembership
      (Op_cat CommRing_cat)
      R
      (@comm_ring_psh_invertibility_sieve
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Struct_sigma V h)))
  : τ (@=
      (@comm_ring_carrier V)
      (@comm_ring_hom_apply
        (@comm_ring_localization_target R s localization)
        V
        (@comm_ring_psh_localization_factor_map_at_member
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s localization V h member)
        (@piapp0
          (@CommRingPshInvertibilityElements_cat
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s)
          (@comm_ring_psh_localization_matching_catd
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s)
          matching
          (@affine_localization_support_center R s localization)))
      (@piapp0
        (@CommRingPshInvertibilityElements_cat
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s)
        (@comm_ring_psh_localization_matching_catd
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s)
        matching
        (@comm_ring_psh_invertibility_element
          (Op_cat CommRing_cat)
          affine_comm_ring_psh
          R s V h member)))
≔ @piapp1_fapp0
    (@CommRingPshInvertibilityElements_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)
    (@comm_ring_psh_localization_matching_catd
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)
    matching
    (@affine_localization_support_center R s localization)
    (@comm_ring_psh_invertibility_element
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s V h member)
    (@affine_localization_center_to_member_arrow
      R s localization V h member);

// Exact right-inverse component type over an arbitrary encoded support
// element.  Keeping the element explicit permits total Sigma elimination.
symbol AffineLocalizationRestrictGlueAtElementPath
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (matching : τ (Obj (@CommRingPshLocalizationMatching_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)))
  (element : τ (Obj (@CommRingPshInvertibilityElements_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)))
  : Grpd
≔ @=
    (Obj (@Fibre_cat
      (@CommRingPshInvertibilityElements_cat
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (@comm_ring_psh_localization_matching_catd
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      element))
    (@piapp0
      (@CommRingPshInvertibilityElements_cat
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (@comm_ring_psh_localization_matching_catd
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (@comm_ring_psh_localization_matching_section
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s localization
        (@fapp0
          (@CommRingPshLocalizationMatching_cat
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s)
          (Path_cat (@comm_ring_carrier
            (@comm_ring_localization_target R s localization)))
          (@affine_localization_matching_glue_func R s localization)
          matching))
      element)
    (@piapp0
      (@CommRingPshInvertibilityElements_cat
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (@comm_ring_psh_localization_matching_catd
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      matching
      element);

/*
  Every encoded support element is a nested Sigma pair `(V,h,member)`.
  Eliminating both packages reduces the goal to the internally derived
  Cartier path above.  The normalized proof-time Yoneda comparison in the
  presheaf owner aligns the stored contravariant family with CommRingHom; no
  package eta or proof-erasure rule is introduced.
*/
symbol affine_localization_restrict_glue_at_element_path
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  (matching : τ (Obj (@CommRingPshLocalizationMatching_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)))
  (element : τ (Obj (@CommRingPshInvertibilityElements_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)))
  : τ (@AffineLocalizationRestrictGlueAtElementPath
      R s localization matching element)
≔ @sigma_ind
    (Obj (@Into_restr_cat (Op_cat CommRing_cat) R))
    (λ q : τ (Obj (@Into_restr_cat (Op_cat CommRing_cat) R)),
      Obj (@Fibre_cat
        (@Into_restr_cat (Op_cat CommRing_cat) R)
        (@sieve_higher
          (Op_cat CommRing_cat)
          R
          (@comm_ring_psh_invertibility_sieve
            (Op_cat CommRing_cat)
            affine_comm_ring_psh
            R s))
        q))
    (λ e : @τΣ_
        (Obj (@Into_restr_cat (Op_cat CommRing_cat) R))
        (λ q : τ (Obj (@Into_restr_cat (Op_cat CommRing_cat) R)),
          Obj (@Fibre_cat
            (@Into_restr_cat (Op_cat CommRing_cat) R)
            (@sieve_higher
              (Op_cat CommRing_cat)
              R
              (@comm_ring_psh_invertibility_sieve
                (Op_cat CommRing_cat)
                affine_comm_ring_psh
                R s))
            q)),
      @AffineLocalizationRestrictGlueAtElementPath
        R s localization matching e)
    (λ q : τ (Obj (@Into_restr_cat (Op_cat CommRing_cat) R)),
      λ member : τ (Obj (@Fibre_cat
          (@Into_restr_cat (Op_cat CommRing_cat) R)
          (@sieve_higher
            (Op_cat CommRing_cat)
            R
            (@comm_ring_psh_invertibility_sieve
              (Op_cat CommRing_cat)
              affine_comm_ring_psh
              R s))
          q)),
        (@sigma_ind
          (Obj (Op_cat (Op_cat CommRing_cat)))
          (λ V : τ (Obj (Op_cat (Op_cat CommRing_cat))),
            Obj (@Fibre_cat
              (Op_cat (Op_cat CommRing_cat))
              (@yoneda_psh (Op_cat CommRing_cat) R)
              V))
          (λ q0 : @τΣ_
              (Obj (Op_cat (Op_cat CommRing_cat)))
              (λ V : τ (Obj (Op_cat (Op_cat CommRing_cat))),
                Obj (@Fibre_cat
                  (Op_cat (Op_cat CommRing_cat))
                  (@yoneda_psh (Op_cat CommRing_cat) R)
                  V)),
            @Pi_grpd
              (Obj (@Fibre_cat
                (@Into_restr_cat (Op_cat CommRing_cat) R)
                (@sieve_higher
                  (Op_cat CommRing_cat)
                  R
                  (@comm_ring_psh_invertibility_sieve
                    (Op_cat CommRing_cat)
                    affine_comm_ring_psh
                    R s))
                q0))
              (λ member0 : τ (Obj (@Fibre_cat
                  (@Into_restr_cat (Op_cat CommRing_cat) R)
                  (@sieve_higher
                    (Op_cat CommRing_cat)
                    R
                    (@comm_ring_psh_invertibility_sieve
                      (Op_cat CommRing_cat)
                      affine_comm_ring_psh
                      R s))
                  q0)),
                @AffineLocalizationRestrictGlueAtElementPath
                  R s localization matching
                  (Struct_sigma q0 member0)))
          (λ V : τ CommRing,
            λ h : τ (@CommRingHom R V),
              λ member0 : τ (@SieveMembership
                  (Op_cat CommRing_cat)
                  R
                  (@comm_ring_psh_invertibility_sieve
                    (Op_cat CommRing_cat)
                    affine_comm_ring_psh
                    R s)
                  (Struct_sigma V h)),
                @affine_localization_matching_cartier_path
                  R s localization matching V h member0)
          q)
        member)
    element;

// Second component law of selected affine glue, now total on support objects.
symbol affine_localization_restrict_glue_component_law
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (@CommRingPshLocalizationRestrictGlueComponentLaw
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s localization
      (@affine_localization_matching_glue_func R s localization))
≔ λ matching : τ (Obj (@CommRingPshLocalizationMatching_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)),
    λ element : τ (Obj (@CommRingPshInvertibilityElements_cat
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)),
      @affine_localization_restrict_glue_at_element_path
        R s localization matching element;

// The selected affine Cartier glue package for every chosen localization.
symbol affine_localization_matching_glue
  [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s))
  : τ (@CommRingPshLocalizationGlue
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s localization)
≔ @comm_ring_psh_localization_glue_intro
    (Op_cat CommRing_cat)
    affine_comm_ring_psh
    R s localization
    (@affine_localization_matching_glue_func R s localization)
    (@affine_localization_glue_restrict_law R s localization)
    (@affine_localization_restrict_glue_component_law R s localization);
