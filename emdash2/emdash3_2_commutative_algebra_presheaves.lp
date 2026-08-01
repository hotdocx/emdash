/*
  Commutative-ring-valued presheaves and semantic invertibility support.

  The presheaf classifier is a transparent ordinary functor category, not a
  second rigid facade.  Values and restrictions therefore expose the actual
  CommRing_cat object and arrow actions.  Generic CommRing_cat identity and
  composition remain opaque on carrier elements; typed paths through the
  selected pointwise identity/composition comparisons provide the explicit
  observation boundary without adding a rewrite or unification rule.

  For a section s in O(U), `CommRingPshInvertibleAlong(O,s,f)` says that the
  restriction O(f)(s) is a unit.  It is proposition-valued and is closed under
  further restriction.  This is the computational predicate underlying the
  future invertibility sieve D(s), but this module does not yet assemble a
  `HigherSieve`, claim sheafhood, or select a Grothendieck topology.
*/

require open emdash.emdash3_2_presheaves;
require open emdash.emdash3_2_commutative_algebra_localization;

// Transparent category of CommRing-valued presheaves on K.
symbol CommRingPsh_cat (K : Cat) : Cat
≔ @Functor_cat (Op_cat K) CommRing_cat;

// Object classifier of CommRing-valued presheaves.
symbol CommRingPsh (K : Cat) : Grpd
≔ Obj (@CommRingPsh_cat K);

// Ring of values O(U).
symbol comm_ring_psh_value
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  : τ CommRing
≔ @fapp0 (Op_cat K) CommRing_cat O U;

// Carrier/type of sections over U.
symbol CommRingPshSection
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  : Grpd
≔ @comm_ring_carrier (@comm_ring_psh_value K O U);

// Structured restriction map O(f) : O(U) -> O(V), for f : V -> U.
symbol comm_ring_psh_restriction_hom
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  : τ (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O V))
≔ @fapp1_fapp0 (Op_cat K) CommRing_cat O U V f;

// Pointwise restriction f^*(s) is application of the actual structured map.
symbol comm_ring_psh_restrict
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (s : τ (@CommRingPshSection K O U))
  : τ (@CommRingPshSection K O V)
≔ @comm_ring_hom_apply
    (@comm_ring_psh_value K O U)
    (@comm_ring_psh_value K O V)
    (@comm_ring_psh_restriction_hom K O V U f)
    s;

/*
  Identity observations.

  `fapp1_id_path` first crosses the opposite-source owner-order boundary;
  `comm_ring_hom_id_pointwise_path` then exposes the selected carrier-level
  identity.  Neither comparison changes the generic whole-arrow normal form.
*/
symbol comm_ring_psh_restriction_id_pointwise_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  : τ (@= (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O U))
      (@comm_ring_psh_restriction_hom K O U U (@id K U))
      (@comm_ring_hom_id_pointwise
        (@comm_ring_psh_value K O U)))
≔ @eq_trans
    (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O U))
    (@comm_ring_psh_restriction_hom K O U U (@id K U))
    (@comm_ring_hom_id
      (@comm_ring_psh_value K O U))
    (@comm_ring_hom_id_pointwise
      (@comm_ring_psh_value K O U))
    (@fapp1_id_path
      (Op_cat K)
      CommRing_cat
      O U)
    (@comm_ring_hom_id_pointwise_path
      (@comm_ring_psh_value K O U));

symbol comm_ring_psh_restrict_id_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  : τ (@= (@CommRingPshSection K O U)
      (@comm_ring_psh_restrict K O U U (@id K U) s)
      s)
≔ @eq_ap
    (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O U))
    (@CommRingPshSection K O U)
    (λ h : τ (@CommRingHom
        (@comm_ring_psh_value K O U)
        (@comm_ring_psh_value K O U)),
      @comm_ring_hom_apply
        (@comm_ring_psh_value K O U)
        (@comm_ring_psh_value K O U)
        h s)
    (@comm_ring_psh_restriction_hom K O U U (@id K U))
    (@comm_ring_hom_id_pointwise
      (@comm_ring_psh_value K O U))
    (@comm_ring_psh_restriction_id_pointwise_path K O U);

/*
  Composite observations.

  For f : V -> U and g : W -> V, the opposite source makes O(g) follow O(f).
  The generic functor theorem reaches whole-map composition, and the existing
  stable pointwise ring-map comparison then makes application compute as
  O(g)(O(f)(s)).
*/
symbol comm_ring_psh_restriction_comp_pointwise_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
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
        (@comm_ring_psh_restriction_hom K O V U f)))
≔ @eq_trans
    (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O W))
    (@comm_ring_psh_restriction_hom K O W U
      (@comp_fapp0 K W V U f g))
    (@comm_ring_hom_comp
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_value K O W)
      (@comm_ring_psh_restriction_hom K O W V g)
      (@comm_ring_psh_restriction_hom K O V U f))
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_value K O W)
      (@comm_ring_psh_restriction_hom K O W V g)
      (@comm_ring_psh_restriction_hom K O V U f))
    (@fapp1_comp_path
      (Op_cat K)
      CommRing_cat
      O
      U V W
      g f)
    (@comm_ring_hom_comp_pointwise_path
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_value K O W)
      (@comm_ring_psh_restriction_hom K O W V g)
      (@comm_ring_psh_restriction_hom K O V U f));

symbol comm_ring_psh_restrict_comp_path
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U))
  : τ (@= (@CommRingPshSection K O W)
      (@comm_ring_psh_restrict K O W U
        (@comp_fapp0 K W V U f g) s)
      (@comm_ring_psh_restrict K O W V g
        (@comm_ring_psh_restrict K O V U f s)))
≔ @eq_ap
    (@CommRingHom
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O W))
    (@CommRingPshSection K O W)
    (λ h : τ (@CommRingHom
        (@comm_ring_psh_value K O U)
        (@comm_ring_psh_value K O W)),
      @comm_ring_hom_apply
        (@comm_ring_psh_value K O U)
        (@comm_ring_psh_value K O W)
        h s)
    (@comm_ring_psh_restriction_hom K O W U
      (@comp_fapp0 K W V U f g))
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_psh_value K O U)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_value K O W)
      (@comm_ring_psh_restriction_hom K O W V g)
      (@comm_ring_psh_restriction_hom K O V U f))
    (@comm_ring_psh_restriction_comp_pointwise_path K O W V U f g);

// Semantic membership predicate for the future invertibility sieve D(s).
symbol CommRingPshInvertibleAlong
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  : Grpd
≔ @CommRingUnitEvidence
    (@comm_ring_psh_value K O V)
    (@comm_ring_psh_restrict K O V U f s);

symbol comm_ring_psh_invertible_along_is_prop
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  : τ (IsPropGrpd (@CommRingPshInvertibleAlong K O U s V f))
≔ @comm_ring_unit_evidence_is_prop
    (@comm_ring_psh_value K O V)
    (@comm_ring_psh_restrict K O V U f s);

// First preserve the unit along O(g), retaining the nested restriction form.
symbol comm_ring_psh_invertible_along_restrict_nested
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U))
  (u : τ (@CommRingPshInvertibleAlong K O U s V f))
  : τ (@CommRingUnitEvidence
      (@comm_ring_psh_value K O W)
      (@comm_ring_psh_restrict K O W V g
        (@comm_ring_psh_restrict K O V U f s)))
≔ @comm_ring_hom_preserves_unit
    (@comm_ring_psh_value K O V)
    (@comm_ring_psh_value K O W)
    (@comm_ring_psh_restriction_hom K O W V g)
    (@comm_ring_psh_restrict K O V U f s)
    u;

// Downward closure under g, transported to the direct composite f ∘ g.
symbol comm_ring_psh_invertible_along_restrict
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [W V U : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (s : τ (@CommRingPshSection K O U))
  (u : τ (@CommRingPshInvertibleAlong K O U s V f))
  : τ (@CommRingPshInvertibleAlong K O U s W
      (@comp_fapp0 K W V U f g))
≔ @comm_ring_unit_transport_backward
    (@comm_ring_psh_value K O W)
    (@comm_ring_psh_restrict K O W U
      (@comp_fapp0 K W V U f g) s)
    (@comm_ring_psh_restrict K O W V g
      (@comm_ring_psh_restrict K O V U f s))
    (@comm_ring_psh_restrict_comp_path K O W V U f g s)
    (@comm_ring_psh_invertible_along_restrict_nested
      K O W V U f g s u);
