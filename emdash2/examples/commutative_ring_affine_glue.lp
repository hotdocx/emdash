/*
  Reviewer-facing computational affine Cartier glue.

  The affine CommRing-valued presheaf on CommRing_cat^op is identity.  For a
  chosen localization i:R->L, evaluation at the canonical support centre
  (L,i) is a glue functor.  Localization uniqueness gives its left inverse
  law, while internal Pi-section action along each universal factor gives the
  componentwise Cartier right inverse.  The final checks instantiate the
  whole selected-glue package at the closed split idempotent in F2 x F2.

  This is selected locality over D(s), not a claim that D(s) covers R or that
  the two functors are equal as whole functors.
*/

require open emdash.emdash3_2_commutative_algebra_affine_glue;
require open emdash.emdash3_2_commutative_algebra_localization_split;

// Values and restrictions of the affine presheaf are the original ring and
// structured map.
assert (R : τ CommRing) ⊢
  @comm_ring_psh_value
    (Op_cat CommRing_cat)
    affine_comm_ring_psh
    R
  ≡ R;

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_psh_restriction_hom
    (Op_cat CommRing_cat)
    affine_comm_ring_psh
    S R h
  ≡ h;

// Matching-section values at the canonical localization centre are elements
// of the selected localization target.
assert [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s)) ⊢
  @Fibre_cat
    (@CommRingPshInvertibilityElements_cat
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)
    (@comm_ring_psh_localization_matching_catd
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      R s)
    (@affine_localization_support_center R s localization)
  ≡ Path_cat (@comm_ring_carrier
      (@comm_ring_localization_target R s localization));

// The centre evaluation is a genuine functor, so matching-arrow action stays
// with the generic functor calculus.
assert [R : τ CommRing]
  [s : τ (@comm_ring_carrier R)]
  (localization : τ (@CommRingLocalizationAt R s)) ⊢
  @affine_localization_matching_glue_func R s localization
  : τ (Functor
      (@CommRingPshLocalizationMatching_cat
        (Op_cat CommRing_cat)
        affine_comm_ring_psh
        R s)
      (Path_cat (@comm_ring_carrier
        (@comm_ring_localization_target R s localization))));

// At a literal support member, the internally carried section action is the
// Cartier factor equation k(glue(m))=m(V,h).
assert [R : τ CommRing]
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
      (Struct_sigma V h))) ⊢
  @affine_localization_matching_cartier_path
    R s localization matching V h member
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
          R s V h member)));

// The non-endpoint split localization inhabits the complete selected affine
// glue package rather than supplying glue as new assumed data.
assert ⊢
  @affine_localization_matching_glue
    f2_split_comm_ring
    f2_split_idempotent
    f2_split_idempotent_localization
  : τ (@CommRingPshLocalizationGlue
      (Op_cat CommRing_cat)
      affine_comm_ring_psh
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_localization);
