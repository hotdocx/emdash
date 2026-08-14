/*
  Integer-facing specialization of the set-truncated telescope localization.

  The carrier localizes the natural-number successor action. A representative
  integer_stage(n,x) has the intended reading x-n. The forward transition is
  integer successor, and the telescope's index shift is its predecessor.

  This module is a transparent, rule-free API over existing HIT owners. It
  does not yet declare addition, signed normal forms, or the universal group
  completion of the additive natural-number monoid.
*/

require open emdash.emdash3_2_nat_arithmetic;
require open emdash.emdash3_2_telescope_localization_hit;

// Integers are the telescope localization of Nat under successor.
symbol Integer_grpd : Grpd
≔ @TelescopeLocalization_grpd Nat_grpd nat_succ_function;

// Readable representative: integer_stage(n,x) denotes the class of (n,x).
symbol integer_stage
  (n x : τ Nat_grpd)
  : τ Integer_grpd
≔ @telescope_localization_inc Nat_grpd nat_succ_function n x;

// Canonical zero representative.
symbol integer_zero
  : τ Integer_grpd
≔ integer_stage zero zero;

// Canonical embedding of a nonnegative integer at stage zero.
symbol integer_of_nat
  (n : τ Nat_grpd)
  : τ Integer_grpd
≔ integer_stage zero n;

// Successor is the localized forward transition.
symbol integer_succ
  : τ (@Function_grpd Integer_grpd Integer_grpd)
≔ @telescope_localization_forward Nat_grpd nat_succ_function;

// Predecessor is the executable index-shift inverse.
symbol integer_pred
  : τ (@Function_grpd Integer_grpd Integer_grpd)
≔ @telescope_localization_inverse Nat_grpd nat_succ_function;

// The whole equality-valued equivalence carried by the localized transition.
symbol integer_succ_omega_equiv
  : τ (@OmegaEquivAlong
      Grpd_cat Integer_grpd Integer_grpd integer_succ)
≔ @telescope_localization_forward_equiv Nat_grpd nat_succ_function;

// Contractible-fibre equivalence used by univalence in the Circle code family.
symbol integer_succ_equiv
  : τ (TypeEquiv Integer_grpd Integer_grpd)
≔ @omega_along_to_type_equiv
    Integer_grpd Integer_grpd integer_succ integer_succ_omega_equiv;

// The integer line inherits the set truncation built into localization.
symbol integer_is_set
  : τ (IsSetGrpd Integer_grpd)
≔ @telescope_localization_is_set Nat_grpd nat_succ_function;
