/*
  Reviewer for global reflective CommRinged objects with a selected cover.

  Constructor projections compute through the existing encoded Sigma owners.
  Pullback coverhood is derived from the selected topology's Grothendieck
  stability, and literal cover members expose their actual domain and arrow.
  No affine, finite, locally-ringed, scheme, or gluing claim is made.
*/

require open emdash.emdash3_2_commutative_algebra_ringed_space_covers;

// The transparent package has exact beta at its primitive projections.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (X : τ (Obj K))
  (R : τ (@Sieve K X))
  (covers : τ (@groth_topology_covers
      K (@reflective_comm_ringed_site_topology K A) X R)) ⊢
  @reflective_comm_ringed_space_cover_ringed_site
    K (@reflective_comm_ringed_space_cover_intro K A X R covers)
  ≡ A;

assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (X : τ (Obj K))
  (R : τ (@Sieve K X))
  (covers : τ (@groth_topology_covers
      K (@reflective_comm_ringed_site_topology K A) X R)) ⊢
  @reflective_comm_ringed_space_cover_whole_object
    K (@reflective_comm_ringed_space_cover_intro K A X R covers)
  ≡ X;

assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (X : τ (Obj K))
  (R : τ (@Sieve K X))
  (covers : τ (@groth_topology_covers
      K (@reflective_comm_ringed_site_topology K A) X R)) ⊢
  @reflective_comm_ringed_space_cover_sieve
    K (@reflective_comm_ringed_space_cover_intro K A X R covers)
  ≡ R;

// The included structure presheaf routes through the selected ringed site.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K)) ⊢
  @reflective_comm_ringed_space_cover_underlying_psh K P
  ≡ @reflective_comm_ringed_site_underlying_psh
      K (@reflective_comm_ringed_space_cover_ringed_site K P);

// Pullback coverhood is the retained Grothendieck stability theorem.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (V : τ (Obj K))
  (f : τ (Hom K V
      (@reflective_comm_ringed_space_cover_whole_object K P))) ⊢
  @reflective_comm_ringed_space_cover_pullback_covers K P V f
  : τ (@groth_topology_covers
      K
      (@reflective_comm_ringed_space_cover_topology K P)
      V
      (@sieve_pullback
        K V
        (@reflective_comm_ringed_space_cover_whole_object K P)
        f
        (@reflective_comm_ringed_space_cover_sieve K P)));

// A literal selected member exposes its actual domain and arrow.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (V : τ (Obj K))
  (f : τ (Hom K V
      (@reflective_comm_ringed_space_cover_whole_object K P)))
  (member : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      (Struct_sigma V f))) ⊢
  @reflective_comm_ringed_space_cover_chart_domain
    K P
    (@reflective_comm_ringed_space_cover_chart_intro
      K P (Struct_sigma V f) member)
  ≡ V;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (V : τ (Obj K))
  (f : τ (Hom K V
      (@reflective_comm_ringed_space_cover_whole_object K P)))
  (member : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      (Struct_sigma V f))) ⊢
  @reflective_comm_ringed_space_cover_chart_arrow
    K P
    (@reflective_comm_ringed_space_cover_chart_intro
      K P (Struct_sigma V f) member)
  ≡ f;

// A selected chart inherits a covering pullback without a cocycle field.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)) ⊢
  @reflective_comm_ringed_space_cover_chart_pullback_covers K P chart
  : τ (@groth_topology_covers
      K
      (@reflective_comm_ringed_space_cover_topology K P)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      (@sieve_pullback
        K
        (@reflective_comm_ringed_space_cover_chart_domain K P chart)
        (@reflective_comm_ringed_space_cover_whole_object K P)
        (@reflective_comm_ringed_space_cover_chart_arrow K P chart)
        (@reflective_comm_ringed_space_cover_sieve K P)));
