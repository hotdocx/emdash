/*
  Reviewer for CommRing-valued presheaves and their invertibility sieve.

  The final zero-ring example constructs unit evidence on every restricted
  section and consumes it through ordinary-sieve membership, so this exercises
  the whole computational assembly rather than merely checking classifiers.
*/

require open emdash.emdash3_2_commutative_algebra_presheaves;
require open emdash.emdash3_2_sites;

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
  Whole-sieve assembly.

  The carrier functor selects a full path-map hom action.  Its application is
  computational through that full action; the direct capped action remains a
  deliberate negative boundary.
*/
assert (R : τ CommRing) ⊢
  @fapp0 CommRing_cat Grpd_cat comm_ring_carrier_func R
  ≡ @comm_ring_carrier R;

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  (@fapp0
    (Path_cat (@CommRingHom R S))
    (Path_cat (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
    (@fapp1_func CommRing_cat Grpd_cat
      comm_ring_carrier_func R S)
    h) x
  ≡ @comm_ring_hom_apply R S h x;

assertnot [R S : τ CommRing]
  (h : τ (@CommRingHom R S)) ⊢
  @fapp1_fapp0 CommRing_cat Grpd_cat
    comm_ring_carrier_func R S h
  ≡ @comm_ring_hom_function R S h;

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @Fibre_cat
    (@Sigma_cat CommRing_cat comm_ring_carrier_catd)
    comm_ring_unit_evidence_total_catd
    (Struct_sigma R x)
  ≡ Path_cat (@CommRingUnitEvidence R x);

// The represented-family variance bridge is proof-time only.
assert [K : Cat]
  (U : τ (Obj K)) ⊢
  @eq_refl
    (Functor (Op_cat K) Cat_cat)
    (@hom_ (Op_cat K) (Op_cat K)
      (@id Cat_cat (Op_cat K)) U)
  : τ (@=
      (Functor (Op_cat K) Cat_cat)
      (@hom_ (Op_cat K) (Op_cat K)
        (@id Cat_cat (Op_cat K)) U)
      (@hom_con K U K (@id Cat_cat K)));

assertnot [K : Cat]
  (U : τ (Obj K)) ⊢
  @hom_ (Op_cat K) (Op_cat K)
    (@id Cat_cat (Op_cat K)) U
  ≡ @hom_con K U K (@id Cat_cat K);

// Literal restriction totals compute to the value ring and restricted section.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  sigma_Fst
    (@fapp0
      (@Into_restr_cat K U)
      (@Sigma_cat CommRing_cat comm_ring_carrier_catd)
      (@comm_ring_psh_restriction_total_func K O U s)
      (Struct_sigma V f))
  ≡ @comm_ring_psh_value K O V;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  sigma_Snd
    (@fapp0
      (@Into_restr_cat K U)
      (@Sigma_cat CommRing_cat comm_ring_carrier_catd)
      (@comm_ring_psh_restriction_total_func K O U s)
      (Struct_sigma V f))
  ≡ @comm_ring_psh_restrict K O V U f s;

// Higher and ordinary membership preserve the arrowwise predicate literally.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @Fibre_cat
    (@Into_restr_cat K U)
    (@comm_ring_psh_invertibility_higher_sieve K O U s)
    (Struct_sigma V f)
  ≡ Path_cat (@CommRingPshInvertibleAlong K O U s V f);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_invertibility_sieve K O U s
  : τ (@Sieve K U);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @SieveMembership
    K U
    (@comm_ring_psh_invertibility_sieve K O U s)
    (Struct_sigma V f)
  ≡ @CommRingPshInvertibleAlong K O U s V f;

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

symbol zero_comm_ring_psh_invertibility_sieve
  [K : Cat]
  (U : τ (Obj K))
  : τ (@Sieve K U)
≔ @comm_ring_psh_invertibility_sieve
    K (@zero_comm_ring_psh K) U tt;

assert (K : Cat) (U : τ (Obj K)) ⊢
  @comm_ring_psh_value K (@zero_comm_ring_psh K) U
  ≡ zero_comm_ring;

assert [K : Cat]
  [V U : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @zero_comm_ring_psh_invertible_along K V U f
  : τ (@CommRingPshInvertibleAlong
      K (@zero_comm_ring_psh K) U tt V f);

// The same concrete witness inhabits membership in the assembled sieve.
assert [K : Cat]
  [V U : τ (Obj K)]
  (f : τ (Hom K V U)) ⊢
  @zero_comm_ring_psh_invertible_along K V U f
  : τ (@SieveMembership
      K U
      (@zero_comm_ring_psh_invertibility_sieve K U)
      (Struct_sigma V f));
