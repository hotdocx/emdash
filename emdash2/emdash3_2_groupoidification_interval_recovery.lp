/*
  Recovery of the completed WalkingArrow--Interval theorem from generic
  groupoidification.

  Generic extension sends the established WalkingArrow interval unit to a map
  Groupoidify(WalkingArrow) -> Interval.  The completed Interval extension
  sends the generic unit in the opposite direction.  Their two cancellations
  are derived from the generic and Interval whole beta/eta laws: restriction
  of a composite is compared through Path_cat_func, the corresponding beta
  identifies its representation, and categorical-HIT uniqueness returns the
  original map.

  No definitional equality between the two groupoids, duplicate interval
  eliminator, source-functorial Groupoidify_func, or adjunction is introduced.
*/

require open emdash.emdash3_2_groupoidification_universality;
require open emdash.emdash3_2_walking_interval_universality;

// The two comparison maps selected by the two whole extension owners.
symbol groupoidify_walking_to_interval
  : τ (@Function_grpd (@Groupoidify WalkingArrow_cat) Interval_grpd)
≔ @groupoidify_extend_at
    WalkingArrow_cat Interval_grpd walking_arrow_to_interval_func;

symbol interval_to_groupoidify_walking
  : τ (@Function_grpd Interval_grpd (@Groupoidify WalkingArrow_cat))
≔ @walking_interval_extend_at
    (@Groupoidify WalkingArrow_cat)
    (@groupoidify_unit_func WalkingArrow_cat);

// Round trips use the ordinary Grpd_cat composition owner.
symbol groupoidify_walking_roundtrip_func
  : τ (@Function_grpd
      (@Groupoidify WalkingArrow_cat)
      (@Groupoidify WalkingArrow_cat))
≔ @comp_fapp0
    Grpd_cat
    (@Groupoidify WalkingArrow_cat)
    Interval_grpd
    (@Groupoidify WalkingArrow_cat)
    interval_to_groupoidify_walking
    groupoidify_walking_to_interval;

symbol interval_groupoidify_roundtrip_func
  : τ (@Function_grpd Interval_grpd Interval_grpd)
≔ @comp_fapp0
    Grpd_cat
    Interval_grpd
    (@Groupoidify WalkingArrow_cat)
    Interval_grpd
    groupoidify_walking_to_interval
    interval_to_groupoidify_walking;

/*
  Restricting the first round trip is definitionally Path(from) composed with
  the generic restriction of to.  Generic beta changes that inner
  representation to the established interval unit; the existing Interval
  restriction comparison then identifies the result with restriction of the
  reverse map.
*/
symbol groupoidify_walking_roundtrip_restrict_to_interval_path
  : τ (@=
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (@groupoidify_restrict_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        groupoidify_walking_roundtrip_func)
      (@walking_interval_restrict_at
        (@Groupoidify WalkingArrow_cat)
        interval_to_groupoidify_walking))
≔ @eq_trans
    (Functor WalkingArrow_cat
      (Path_cat (@Groupoidify WalkingArrow_cat)))
    (@comp_cat_fapp0
      WalkingArrow_cat
      (Path_cat Interval_grpd)
      (Path_cat (@Groupoidify WalkingArrow_cat))
      (@path_map_func
        Interval_grpd
        (@Groupoidify WalkingArrow_cat)
        interval_to_groupoidify_walking)
      (@groupoidify_restrict_at
        WalkingArrow_cat
        Interval_grpd
        groupoidify_walking_to_interval))
    (@comp_cat_fapp0
      WalkingArrow_cat
      (Path_cat Interval_grpd)
      (Path_cat (@Groupoidify WalkingArrow_cat))
      (@path_map_func
        Interval_grpd
        (@Groupoidify WalkingArrow_cat)
        interval_to_groupoidify_walking)
      walking_arrow_to_interval_func)
    (@walking_interval_restrict_at
      (@Groupoidify WalkingArrow_cat)
      interval_to_groupoidify_walking)
    (@eq_ap
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (λ F : τ (Functor WalkingArrow_cat (Path_cat Interval_grpd)),
        @comp_cat_fapp0
          WalkingArrow_cat
          (Path_cat Interval_grpd)
          (Path_cat (@Groupoidify WalkingArrow_cat))
          (@path_map_func
            Interval_grpd
            (@Groupoidify WalkingArrow_cat)
            interval_to_groupoidify_walking)
          F)
      (@groupoidify_restrict_at
        WalkingArrow_cat
        Interval_grpd
        groupoidify_walking_to_interval)
      walking_arrow_to_interval_func
      (@groupoidify_restrict_extend_beta_at_path
        WalkingArrow_cat
        Interval_grpd
        walking_arrow_to_interval_func))
    (@eq_sym
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (@walking_interval_restrict_at
        (@Groupoidify WalkingArrow_cat)
        interval_to_groupoidify_walking)
      (@comp_cat_fapp0
        WalkingArrow_cat
        (Path_cat Interval_grpd)
        (Path_cat (@Groupoidify WalkingArrow_cat))
        (@path_map_func
          Interval_grpd
          (@Groupoidify WalkingArrow_cat)
          interval_to_groupoidify_walking)
        walking_arrow_to_interval_func)
      (@walking_interval_restrict_at_path
        (@Groupoidify WalkingArrow_cat)
        interval_to_groupoidify_walking));

// Interval beta completes the restricted first round trip to the generic unit.
symbol groupoidify_walking_roundtrip_restrict_path
  : τ (@=
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (@groupoidify_restrict_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        groupoidify_walking_roundtrip_func)
      (@groupoidify_unit_func WalkingArrow_cat))
≔ @eq_trans
    (Functor WalkingArrow_cat
      (Path_cat (@Groupoidify WalkingArrow_cat)))
    (@groupoidify_restrict_at
      WalkingArrow_cat
      (@Groupoidify WalkingArrow_cat)
      groupoidify_walking_roundtrip_func)
    (@walking_interval_restrict_at
      (@Groupoidify WalkingArrow_cat)
      interval_to_groupoidify_walking)
    (@groupoidify_unit_func WalkingArrow_cat)
    groupoidify_walking_roundtrip_restrict_to_interval_path
    (@walking_interval_restrict_extend_beta_at_path
      (@Groupoidify WalkingArrow_cat)
      (@groupoidify_unit_func WalkingArrow_cat));

// Restriction of identity compares to the generic unit through its literal
// Path-map/precomposition presentation.
symbol groupoidify_walking_restrict_id_path
  : τ (@=
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (@groupoidify_restrict_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@id Grpd_cat (@Groupoidify WalkingArrow_cat)))
      (@groupoidify_unit_func WalkingArrow_cat))
≔ @groupoidify_restrict_at_path
    WalkingArrow_cat
    (@Groupoidify WalkingArrow_cat)
    (@id Grpd_cat (@Groupoidify WalkingArrow_cat));

// Therefore the two restricted maps agree.
symbol groupoidify_walking_roundtrip_restrict_id_path
  : τ (@=
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (@groupoidify_restrict_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        groupoidify_walking_roundtrip_func)
      (@groupoidify_restrict_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@id Grpd_cat (@Groupoidify WalkingArrow_cat))))
≔ @eq_trans
    (Functor WalkingArrow_cat
      (Path_cat (@Groupoidify WalkingArrow_cat)))
    (@groupoidify_restrict_at
      WalkingArrow_cat
      (@Groupoidify WalkingArrow_cat)
      groupoidify_walking_roundtrip_func)
    (@groupoidify_unit_func WalkingArrow_cat)
    (@groupoidify_restrict_at
      WalkingArrow_cat
      (@Groupoidify WalkingArrow_cat)
      (@id Grpd_cat (@Groupoidify WalkingArrow_cat)))
    groupoidify_walking_roundtrip_restrict_path
    (@eq_sym
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (@groupoidify_restrict_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@id Grpd_cat (@Groupoidify WalkingArrow_cat)))
      (@groupoidify_unit_func WalkingArrow_cat)
      groupoidify_walking_restrict_id_path);

// Congruence of generic extension transports the restricted comparison.
symbol groupoidify_walking_roundtrip_extension_path
  : τ (@=
      (@Function_grpd
        (@Groupoidify WalkingArrow_cat)
        (@Groupoidify WalkingArrow_cat))
      (@groupoidify_extend_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@groupoidify_restrict_at
          WalkingArrow_cat
          (@Groupoidify WalkingArrow_cat)
          groupoidify_walking_roundtrip_func))
      (@groupoidify_extend_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@groupoidify_restrict_at
          WalkingArrow_cat
          (@Groupoidify WalkingArrow_cat)
          (@id Grpd_cat (@Groupoidify WalkingArrow_cat)))))
≔ @eq_ap
    (Functor WalkingArrow_cat
      (Path_cat (@Groupoidify WalkingArrow_cat)))
    (@Function_grpd
      (@Groupoidify WalkingArrow_cat)
      (@Groupoidify WalkingArrow_cat))
    (@groupoidify_extend_at
      WalkingArrow_cat
      (@Groupoidify WalkingArrow_cat))
    (@groupoidify_restrict_at
      WalkingArrow_cat
      (@Groupoidify WalkingArrow_cat)
      groupoidify_walking_roundtrip_func)
    (@groupoidify_restrict_at
      WalkingArrow_cat
      (@Groupoidify WalkingArrow_cat)
      (@id Grpd_cat (@Groupoidify WalkingArrow_cat)))
    groupoidify_walking_roundtrip_restrict_id_path;

// Generic eta on the round trip and on identity proves the first cancellation.
symbol groupoidify_walking_roundtrip_cancel_path
  : τ (@=
      (@Function_grpd
        (@Groupoidify WalkingArrow_cat)
        (@Groupoidify WalkingArrow_cat))
      groupoidify_walking_roundtrip_func
      (@id Grpd_cat (@Groupoidify WalkingArrow_cat)))
≔ @eq_trans
    (@Function_grpd
      (@Groupoidify WalkingArrow_cat)
      (@Groupoidify WalkingArrow_cat))
    groupoidify_walking_roundtrip_func
    (@groupoidify_extend_at
      WalkingArrow_cat
      (@Groupoidify WalkingArrow_cat)
      (@groupoidify_restrict_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        groupoidify_walking_roundtrip_func))
    (@id Grpd_cat (@Groupoidify WalkingArrow_cat))
    (@eq_sym
      (@Function_grpd
        (@Groupoidify WalkingArrow_cat)
        (@Groupoidify WalkingArrow_cat))
      (@groupoidify_extend_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@groupoidify_restrict_at
          WalkingArrow_cat
          (@Groupoidify WalkingArrow_cat)
          groupoidify_walking_roundtrip_func))
      groupoidify_walking_roundtrip_func
      (@groupoidify_extend_restrict_eta_at_path
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        groupoidify_walking_roundtrip_func))
    (@eq_trans
      (@Function_grpd
        (@Groupoidify WalkingArrow_cat)
        (@Groupoidify WalkingArrow_cat))
      (@groupoidify_extend_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@groupoidify_restrict_at
          WalkingArrow_cat
          (@Groupoidify WalkingArrow_cat)
          groupoidify_walking_roundtrip_func))
      (@groupoidify_extend_at
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@groupoidify_restrict_at
          WalkingArrow_cat
          (@Groupoidify WalkingArrow_cat)
          (@id Grpd_cat (@Groupoidify WalkingArrow_cat))))
      (@id Grpd_cat (@Groupoidify WalkingArrow_cat))
      groupoidify_walking_roundtrip_extension_path
      (@groupoidify_extend_restrict_eta_at_path
        WalkingArrow_cat
        (@Groupoidify WalkingArrow_cat)
        (@id Grpd_cat (@Groupoidify WalkingArrow_cat))));

/*
  The reverse cancellation is symmetric.  Interval beta first changes the
  restricted reverse map to the generic unit; generic beta then changes the
  resulting representation to the established interval unit.
*/
symbol interval_groupoidify_roundtrip_restrict_to_generic_path
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (@walking_interval_restrict_at
        Interval_grpd
        interval_groupoidify_roundtrip_func)
      (@groupoidify_restrict_at
        WalkingArrow_cat
        Interval_grpd
        groupoidify_walking_to_interval))
≔ @eq_trans
    (Functor WalkingArrow_cat (Path_cat Interval_grpd))
    (@comp_cat_fapp0
      WalkingArrow_cat
      (Path_cat (@Groupoidify WalkingArrow_cat))
      (Path_cat Interval_grpd)
      (@path_map_func
        (@Groupoidify WalkingArrow_cat)
        Interval_grpd
        groupoidify_walking_to_interval)
      (@walking_interval_restrict_at
        (@Groupoidify WalkingArrow_cat)
        interval_to_groupoidify_walking))
    (@comp_cat_fapp0
      WalkingArrow_cat
      (Path_cat (@Groupoidify WalkingArrow_cat))
      (Path_cat Interval_grpd)
      (@path_map_func
        (@Groupoidify WalkingArrow_cat)
        Interval_grpd
        groupoidify_walking_to_interval)
      (@groupoidify_unit_func WalkingArrow_cat))
    (@groupoidify_restrict_at
      WalkingArrow_cat
      Interval_grpd
      groupoidify_walking_to_interval)
    (@eq_ap
      (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat)))
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (λ F : τ (Functor WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat))),
        @comp_cat_fapp0
          WalkingArrow_cat
          (Path_cat (@Groupoidify WalkingArrow_cat))
          (Path_cat Interval_grpd)
          (@path_map_func
            (@Groupoidify WalkingArrow_cat)
            Interval_grpd
            groupoidify_walking_to_interval)
          F)
      (@walking_interval_restrict_at
        (@Groupoidify WalkingArrow_cat)
        interval_to_groupoidify_walking)
      (@groupoidify_unit_func WalkingArrow_cat)
      (@walking_interval_restrict_extend_beta_at_path
        (@Groupoidify WalkingArrow_cat)
        (@groupoidify_unit_func WalkingArrow_cat)))
    (@eq_sym
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (@groupoidify_restrict_at
        WalkingArrow_cat
        Interval_grpd
        groupoidify_walking_to_interval)
      (@comp_cat_fapp0
        WalkingArrow_cat
        (Path_cat (@Groupoidify WalkingArrow_cat))
        (Path_cat Interval_grpd)
        (@path_map_func
          (@Groupoidify WalkingArrow_cat)
          Interval_grpd
          groupoidify_walking_to_interval)
        (@groupoidify_unit_func WalkingArrow_cat))
      (@groupoidify_restrict_at_path
        WalkingArrow_cat
        Interval_grpd
        groupoidify_walking_to_interval));

symbol interval_groupoidify_roundtrip_restrict_path
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (@walking_interval_restrict_at
        Interval_grpd
        interval_groupoidify_roundtrip_func)
      walking_arrow_to_interval_func)
≔ @eq_trans
    (Functor WalkingArrow_cat (Path_cat Interval_grpd))
    (@walking_interval_restrict_at
      Interval_grpd
      interval_groupoidify_roundtrip_func)
    (@groupoidify_restrict_at
      WalkingArrow_cat
      Interval_grpd
      groupoidify_walking_to_interval)
    walking_arrow_to_interval_func
    interval_groupoidify_roundtrip_restrict_to_generic_path
    (@groupoidify_restrict_extend_beta_at_path
      WalkingArrow_cat
      Interval_grpd
      walking_arrow_to_interval_func);

symbol interval_restrict_id_path
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (@walking_interval_restrict_at
        Interval_grpd
        (@id Grpd_cat Interval_grpd))
      walking_arrow_to_interval_func)
≔ @walking_interval_restrict_at_path
    Interval_grpd
    (@id Grpd_cat Interval_grpd);

symbol interval_groupoidify_roundtrip_restrict_id_path
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (@walking_interval_restrict_at
        Interval_grpd
        interval_groupoidify_roundtrip_func)
      (@walking_interval_restrict_at
        Interval_grpd
        (@id Grpd_cat Interval_grpd)))
≔ @eq_trans
    (Functor WalkingArrow_cat (Path_cat Interval_grpd))
    (@walking_interval_restrict_at
      Interval_grpd
      interval_groupoidify_roundtrip_func)
    walking_arrow_to_interval_func
    (@walking_interval_restrict_at
      Interval_grpd
      (@id Grpd_cat Interval_grpd))
    interval_groupoidify_roundtrip_restrict_path
    (@eq_sym
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      (@walking_interval_restrict_at
        Interval_grpd
        (@id Grpd_cat Interval_grpd))
      walking_arrow_to_interval_func
      interval_restrict_id_path);

symbol interval_groupoidify_roundtrip_extension_path
  : τ (@=
      (@Function_grpd Interval_grpd Interval_grpd)
      (@walking_interval_extend_at
        Interval_grpd
        (@walking_interval_restrict_at
          Interval_grpd
          interval_groupoidify_roundtrip_func))
      (@walking_interval_extend_at
        Interval_grpd
        (@walking_interval_restrict_at
          Interval_grpd
          (@id Grpd_cat Interval_grpd))))
≔ @eq_ap
    (Functor WalkingArrow_cat (Path_cat Interval_grpd))
    (@Function_grpd Interval_grpd Interval_grpd)
    (@walking_interval_extend_at Interval_grpd)
    (@walking_interval_restrict_at
      Interval_grpd
      interval_groupoidify_roundtrip_func)
    (@walking_interval_restrict_at
      Interval_grpd
      (@id Grpd_cat Interval_grpd))
    interval_groupoidify_roundtrip_restrict_id_path;

// Interval eta on the round trip and on identity proves the second cancellation.
symbol interval_groupoidify_roundtrip_cancel_path
  : τ (@=
      (@Function_grpd Interval_grpd Interval_grpd)
      interval_groupoidify_roundtrip_func
      (@id Grpd_cat Interval_grpd))
≔ @eq_trans
    (@Function_grpd Interval_grpd Interval_grpd)
    interval_groupoidify_roundtrip_func
    (@walking_interval_extend_at
      Interval_grpd
      (@walking_interval_restrict_at
        Interval_grpd
        interval_groupoidify_roundtrip_func))
    (@id Grpd_cat Interval_grpd)
    (@eq_sym
      (@Function_grpd Interval_grpd Interval_grpd)
      (@walking_interval_extend_at
        Interval_grpd
        (@walking_interval_restrict_at
          Interval_grpd
          interval_groupoidify_roundtrip_func))
      interval_groupoidify_roundtrip_func
      (@walking_interval_extend_restrict_eta_at_path
        Interval_grpd
        interval_groupoidify_roundtrip_func))
    (@eq_trans
      (@Function_grpd Interval_grpd Interval_grpd)
      (@walking_interval_extend_at
        Interval_grpd
        (@walking_interval_restrict_at
          Interval_grpd
          interval_groupoidify_roundtrip_func))
      (@walking_interval_extend_at
        Interval_grpd
        (@walking_interval_restrict_at
          Interval_grpd
          (@id Grpd_cat Interval_grpd)))
      (@id Grpd_cat Interval_grpd)
      interval_groupoidify_roundtrip_extension_path
      (@walking_interval_extend_restrict_eta_at_path
        Interval_grpd
        (@id Grpd_cat Interval_grpd)));

// The categorical identity and the stable pointwise identity are compared by
// the existing proof-time Grpd_cat rule.  Re-targeting the whole cancellations
// to grpd_id_function makes their pointwise views compute.
symbol groupoidify_walking_id_function_path
  : τ (@=
      (@Function_grpd
        (@Groupoidify WalkingArrow_cat)
        (@Groupoidify WalkingArrow_cat))
      (@id Grpd_cat (@Groupoidify WalkingArrow_cat))
      (@grpd_id_function (@Groupoidify WalkingArrow_cat)))
≔ @eq_refl
    (@Function_grpd
      (@Groupoidify WalkingArrow_cat)
      (@Groupoidify WalkingArrow_cat))
    (@id Grpd_cat (@Groupoidify WalkingArrow_cat));

symbol interval_id_function_path
  : τ (@=
      (@Function_grpd Interval_grpd Interval_grpd)
      (@id Grpd_cat Interval_grpd)
      (@grpd_id_function Interval_grpd))
≔ @eq_refl
    (@Function_grpd Interval_grpd Interval_grpd)
    (@id Grpd_cat Interval_grpd);

symbol groupoidify_walking_roundtrip_pointwise_path
  : τ (@=
      (@Function_grpd
        (@Groupoidify WalkingArrow_cat)
        (@Groupoidify WalkingArrow_cat))
      groupoidify_walking_roundtrip_func
      (@grpd_id_function (@Groupoidify WalkingArrow_cat)))
≔ @eq_trans
    (@Function_grpd
      (@Groupoidify WalkingArrow_cat)
      (@Groupoidify WalkingArrow_cat))
    groupoidify_walking_roundtrip_func
    (@id Grpd_cat (@Groupoidify WalkingArrow_cat))
    (@grpd_id_function (@Groupoidify WalkingArrow_cat))
    groupoidify_walking_roundtrip_cancel_path
    groupoidify_walking_id_function_path;

symbol interval_groupoidify_roundtrip_pointwise_path
  : τ (@=
      (@Function_grpd Interval_grpd Interval_grpd)
      interval_groupoidify_roundtrip_func
      (@grpd_id_function Interval_grpd))
≔ @eq_trans
    (@Function_grpd Interval_grpd Interval_grpd)
    interval_groupoidify_roundtrip_func
    (@id Grpd_cat Interval_grpd)
    (@grpd_id_function Interval_grpd)
    interval_groupoidify_roundtrip_cancel_path
    interval_id_function_path;

// Pointwise views of the two whole cancellations.
symbol groupoidify_walking_roundtrip_cancel_at
  (u : τ (@Groupoidify WalkingArrow_cat))
  : τ (@=
      (@Groupoidify WalkingArrow_cat)
      (interval_to_groupoidify_walking
        (groupoidify_walking_to_interval u))
      u)
≔ @eq_ap
    (@Function_grpd
      (@Groupoidify WalkingArrow_cat)
      (@Groupoidify WalkingArrow_cat))
    (@Groupoidify WalkingArrow_cat)
    (λ h : τ (@Function_grpd
      (@Groupoidify WalkingArrow_cat)
      (@Groupoidify WalkingArrow_cat)), h u)
    groupoidify_walking_roundtrip_func
    (@grpd_id_function (@Groupoidify WalkingArrow_cat))
    groupoidify_walking_roundtrip_pointwise_path;

symbol interval_groupoidify_roundtrip_cancel_at
  (i : τ Interval_grpd)
  : τ (@=
      Interval_grpd
      (groupoidify_walking_to_interval
        (interval_to_groupoidify_walking i))
      i)
≔ @eq_ap
    (@Function_grpd Interval_grpd Interval_grpd)
    Interval_grpd
    (λ h : τ (@Function_grpd Interval_grpd Interval_grpd), h i)
    interval_groupoidify_roundtrip_func
    (@grpd_id_function Interval_grpd)
    interval_groupoidify_roundtrip_pointwise_path;

// The two cancellation paths package an explicit groupoid equivalence.
symbol groupoidify_walking_interval_by_inverse
  : τ (@EquivByInverse
      (@Groupoidify WalkingArrow_cat)
      Interval_grpd
      groupoidify_walking_to_interval
      interval_to_groupoidify_walking)
≔ @Product_pair_grpd
    (@Pi_grpd
      (@Groupoidify WalkingArrow_cat)
      (λ u : τ (@Groupoidify WalkingArrow_cat),
        @= (@Groupoidify WalkingArrow_cat)
          (interval_to_groupoidify_walking
            (groupoidify_walking_to_interval u))
          u))
    (@Pi_grpd
      Interval_grpd
      (λ i : τ Interval_grpd,
        @= Interval_grpd
          (groupoidify_walking_to_interval
            (interval_to_groupoidify_walking i))
          i))
    groupoidify_walking_roundtrip_cancel_at
    interval_groupoidify_roundtrip_cancel_at;

symbol groupoidify_walking_interval_type_equiv
  : τ (@TypeEquiv (@Groupoidify WalkingArrow_cat) Interval_grpd)
≔ @Struct_sigma
    (@Function_grpd (@Groupoidify WalkingArrow_cat) Interval_grpd)
    (λ f : τ (@Function_grpd
      (@Groupoidify WalkingArrow_cat) Interval_grpd),
      @IsEquivMap (@Groupoidify WalkingArrow_cat) Interval_grpd f)
    groupoidify_walking_to_interval
    (@is_equiv_map_by_inverse
      (@Groupoidify WalkingArrow_cat)
      Interval_grpd
      groupoidify_walking_to_interval
      interval_to_groupoidify_walking
      groupoidify_walking_interval_by_inverse);
