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

// Canonical negative-one representative at the first telescope stage.
symbol integer_neg_one
  : τ Integer_grpd
≔ integer_stage (succ zero) zero;

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

// Universe path whose transport is propositionally the integer successor.
symbol integer_succ_path
  : τ (@= Grpd_grpd Integer_grpd Integer_grpd)
≔ @grpd_equiv_path Integer_grpd Integer_grpd integer_succ_equiv;

// The telescope generator specialized to the integer stage presentation.
symbol integer_stage_step
  (n x : τ Nat_grpd)
  : τ (@= Integer_grpd
      (integer_stage (succ n) (succ x))
      (integer_stage n x))
≔ @telescope_localization_step Nat_grpd nat_succ_function n x;

// Successor after predecessor is propositionally the identity.
symbol integer_succ_pred
  (z : τ Integer_grpd)
  : τ (@= Integer_grpd (integer_succ (integer_pred z)) z)
≔ @telescope_localization_forward_inverse_point
    Nat_grpd nat_succ_function z;

// Predecessor after successor is propositionally the identity.
symbol integer_pred_succ
  (z : τ Integer_grpd)
  : τ (@= Integer_grpd (integer_pred (integer_succ z)) z)
≔ @telescope_localization_inverse_forward_point
    Nat_grpd nat_succ_function z;

// Transport along the selected universe path agrees with successor.
symbol integer_succ_path_coe
  (z : τ Integer_grpd)
  : τ (@= Integer_grpd
      (@coe_grpd
        Integer_grpd Integer_grpd integer_succ_path z)
      (integer_succ z))
≔ @grpd_equiv_path_coe
    Integer_grpd Integer_grpd integer_succ_equiv z;

// The first negative representative is sent back to zero by successor.
symbol integer_succ_neg_one
  : τ (@= Integer_grpd
      (integer_succ integer_neg_one)
      integer_zero)
≔ integer_stage_step zero zero;

/*
  Integer-facing dependent induction. The fibres are set-valued because the
  trusted carrier is the set-truncated telescope HIT. Circle will supply this
  condition for its path-valued decode motive from its one-dimensional
  signature; no stronger elimination principle is asserted here.
*/
symbol integer_ind
  (D : τ Integer_grpd → Grpd)
  (hD : Π z : τ Integer_grpd, τ (IsSetGrpd (D z)))
  (d : Π n : τ Nat_grpd,
    Π x : τ Nat_grpd,
      τ (D (integer_stage n x)))
  (coh : Π n : τ Nat_grpd,
    Π x : τ Nat_grpd,
      τ (@PathOver
        Integer_grpd
        D
        (integer_stage (succ n) (succ x))
        (integer_stage n x)
        (integer_stage_step n x)
        (d (succ n) (succ x))
        (d n x)))
  (z : τ Integer_grpd)
  : τ (D z)
≔ @telescope_localization_ind
    Nat_grpd nat_succ_function D hD d coh z;

// Nondependent set-valued elimination with an ordinary stage-step equation.
symbol integer_elim
  [B : Grpd]
  (hB : τ (IsSetGrpd B))
  (d : Π n : τ Nat_grpd, Π x : τ Nat_grpd, τ B)
  (coh : Π n : τ Nat_grpd,
    Π x : τ Nat_grpd,
      τ (@= B (d (succ n) (succ x)) (d n x)))
  (z : τ Integer_grpd)
  : τ B
≔ @integer_ind
    (λ _ : τ Integer_grpd, B)
    (λ _ : τ Integer_grpd, hB)
    d
    (λ n : τ Nat_grpd,
      λ x : τ Nat_grpd,
        @const_pathover
          Integer_grpd
          B
          (integer_stage (succ n) (succ x))
          (integer_stage n x)
          (d (succ n) (succ x))
          (d n x)
          (integer_stage_step n x)
          (coh n x))
    z;

// The integer line inherits the set truncation built into localization.
symbol integer_is_set
  : τ (IsSetGrpd Integer_grpd)
≔ @telescope_localization_is_set Nat_grpd nat_succ_function;
