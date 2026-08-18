/*
  Reviewer for recovery of the WalkingArrow interval from generic
  groupoidification.
*/

require open emdash.emdash3_2_groupoidification_interval_recovery;

// The comparison maps are selected by the generic and Interval extensions.
assert ⊢ groupoidify_walking_to_interval
  : τ (Function_grpd (Groupoidify WalkingArrow_cat) Interval_grpd);

assert ⊢ groupoidify_walking_to_interval
  ≡ @groupoidify_extend_at
      WalkingArrow_cat Interval_grpd walking_arrow_to_interval_func;

assert ⊢ interval_to_groupoidify_walking
  : τ (Function_grpd Interval_grpd (Groupoidify WalkingArrow_cat));

assert ⊢ interval_to_groupoidify_walking
  ≡ @walking_interval_extend_at
      (Groupoidify WalkingArrow_cat)
      (@groupoidify_unit_func WalkingArrow_cat);

// Both whole round trips cancel by the two mapping-object uniqueness laws.
assert ⊢ groupoidify_walking_roundtrip_cancel_path
  : τ (@=
      (Function_grpd
        (Groupoidify WalkingArrow_cat)
        (Groupoidify WalkingArrow_cat))
      groupoidify_walking_roundtrip_func
      (@id Grpd_cat (Groupoidify WalkingArrow_cat)));

assert ⊢ interval_groupoidify_roundtrip_cancel_path
  : τ (@=
      (Function_grpd Interval_grpd Interval_grpd)
      interval_groupoidify_roundtrip_func
      (@id Grpd_cat Interval_grpd));

// Their pointwise forms have the ordinary quasi-inverse endpoints.
assert (u : τ (Groupoidify WalkingArrow_cat)) ⊢
  groupoidify_walking_roundtrip_cancel_at u
  : τ (@=
      (Groupoidify WalkingArrow_cat)
      (interval_to_groupoidify_walking
        (groupoidify_walking_to_interval u))
      u);

assert (i : τ Interval_grpd) ⊢
  interval_groupoidify_roundtrip_cancel_at i
  : τ (@=
      Interval_grpd
      (groupoidify_walking_to_interval
        (interval_to_groupoidify_walking i))
      i);

assert ⊢ groupoidify_walking_interval_by_inverse
  : τ (@EquivByInverse
      (Groupoidify WalkingArrow_cat)
      Interval_grpd
      groupoidify_walking_to_interval
      interval_to_groupoidify_walking);

assert ⊢ groupoidify_walking_interval_type_equiv
  : τ (TypeEquiv (Groupoidify WalkingArrow_cat) Interval_grpd);

assert ⊢
  @type_equiv_to
    (Groupoidify WalkingArrow_cat)
    Interval_grpd
    groupoidify_walking_interval_type_equiv
  ≡ groupoidify_walking_to_interval;

// Recovery is equivalence, not a new definitional identification of HITs.
assertnot ⊢ Groupoidify WalkingArrow_cat ≡ Interval_grpd;
