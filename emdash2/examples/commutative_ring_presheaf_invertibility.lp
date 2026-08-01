/*
  Reviewer for CommRing-valued presheaves and invertibility support.

  The final zero-ring example constructs unit evidence on every restricted
  section, so this exercises the computational predicate rather than merely
  checking its classifier.
*/

require open emdash.emdash3_2_commutative_algebra_presheaves;

// The classifier is intentionally a transparent functor category.
assert (K : Cat) ⊢
  @CommRingPsh_cat K
  ≡ @Functor_cat (Op_cat K) CommRing_cat;

assert (K : Cat) ⊢
  @CommRingPsh K
  ≡ Functor (Op_cat K) CommRing_cat;

// Values and restrictions expose the actual ordinary functor action.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K)) ⊢
  @comm_ring_psh_value K O U
  ≡ @fapp0 (Op_cat K) CommRing_cat O U;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @comm_ring_psh_restriction_hom K O V U f
  ≡ @fapp1_fapp0 (Op_cat K) CommRing_cat O U V f;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict K O V U f s
  ≡ @comm_ring_hom_apply
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_restriction_hom K O V U f)
      s;

// The abstract identity theorem survives specialization to the opposite base.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K)) ⊢
  @fapp1_id_path (Op_cat K) CommRing_cat O U
  : τ (@=
      (@CommRingHom
        (@comm_ring_psh_value K O U)
        (@comm_ring_psh_value K O U))
      (@comm_ring_psh_restriction_hom K O U U (@id K U))
      (@comm_ring_hom_id (@comm_ring_psh_value K O U)));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict_id_path K O U s
  : τ (@= (@CommRingPshSection K O U)
      (@comm_ring_psh_restrict K O U U (@id K U) s)
      s);

// Generic CommRing_cat identity remains opaque on carrier elements.
assertnot [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict K O U U (@id K U) s
  ≡ s;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V)) ⊢
  @comm_ring_psh_restriction_comp_pointwise_path K O W V U f g
  : τ (@= (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O W))
      (@comm_ring_psh_restriction_hom K O W U
        (@comp_fapp0 K W V U f g))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_psh_value K O U)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_value K O W)
        (@comm_ring_psh_restriction_hom K O W V g)
        (@comm_ring_psh_restriction_hom K O V U f)));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict_comp_path K O W V U f g s
  : τ (@= (@CommRingPshSection K O W)
      (@comm_ring_psh_restrict K O W U
        (@comp_fapp0 K W V U f g) s)
      (@comm_ring_psh_restrict K O W V g
        (@comm_ring_psh_restrict K O V U f s)));

// Composite restriction is observed by a path, not a new carrier rewrite.
assertnot [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_restrict K O W U
    (@comp_fapp0 K W V U f g) s
  ≡ @comm_ring_psh_restrict K O W V g
      (@comm_ring_psh_restrict K O V U f s);

// Unit preservation retains a computationally visible mapped inverse.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [x : τ (@comm_ring_carrier R)]
  (u : τ (@CommRingUnitEvidence R x)) ⊢
  @comm_ring_unit_inverse
    S
    (@comm_ring_hom_apply R S h x)
    (@comm_ring_hom_preserves_unit R S h x u)
  ≡ @comm_ring_hom_apply R S h
      (@comm_ring_unit_inverse R x u);

// Invertibility along f is exactly unit evidence for the restricted section.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @CommRingPshInvertibleAlong K O U s V f
  ≡ @CommRingUnitEvidence
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_restrict K O V U f s);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_invertible_along_is_prop K O U s V f
  : τ (IsPropGrpd (@CommRingPshInvertibleAlong K O U s V f));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U))
  (u : τ (@CommRingPshInvertibleAlong K O U s V f)) ⊢
  @comm_ring_psh_invertible_along_restrict K O W V U f g s u
  : τ (@CommRingPshInvertibleAlong K O U s W
      (@comp_fapp0 K W V U f g));

/*
  Concrete zero-ring model.

  The constant presheaf has a generic CommRing_cat identity as every
  restriction.  The selected identity path computes its action on tt, after
  which the explicit zero-ring unit witness transports to every arrow.
*/
symbol zero_comm_ring_psh
  (K : Cat)
  : τ (@CommRingPsh K)
≔ @Const_func (Op_cat K) CommRing_cat zero_comm_ring;

symbol zero_comm_ring_tt_unit
  : τ (@CommRingUnitEvidence zero_comm_ring tt)
≔ @comm_ring_unit_intro
    zero_comm_ring tt tt (@eq_refl Unit_grpd tt);

symbol zero_comm_ring_psh_restrict_path
  [K : Cat]
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  : τ (@= Unit_grpd
      (@comm_ring_psh_restrict K (@zero_comm_ring_psh K) V U f tt)
      tt)
≔ @eq_ap
    (@CommRingHom zero_comm_ring zero_comm_ring)
    Unit_grpd
    (λ h : τ (@CommRingHom zero_comm_ring zero_comm_ring),
      @comm_ring_hom_apply zero_comm_ring zero_comm_ring h tt)
    (@comm_ring_psh_restriction_hom
      K (@zero_comm_ring_psh K) V U f)
    (@comm_ring_hom_id_pointwise zero_comm_ring)
    (@comm_ring_hom_id_pointwise_path zero_comm_ring);

symbol zero_comm_ring_psh_invertible_along
  [K : Cat]
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  : τ (@CommRingPshInvertibleAlong
      K (@zero_comm_ring_psh K) U tt V f)
≔ @comm_ring_unit_transport_backward
    zero_comm_ring
    (@comm_ring_psh_restrict K (@zero_comm_ring_psh K) V U f tt)
    tt
    (@zero_comm_ring_psh_restrict_path K V U f)
    zero_comm_ring_tt_unit;

assert (K : Cat) (U : τ (Obj K)) ⊢
  @comm_ring_psh_value K (@zero_comm_ring_psh K) U
  ≡ zero_comm_ring;

assert [K : Cat]
  [V U : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @zero_comm_ring_psh_invertible_along K V U f
  : τ (@CommRingPshInvertibleAlong
      K (@zero_comm_ring_psh K) U tt V f);
