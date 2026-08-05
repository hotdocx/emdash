/*
  Reviewer for whole ambient restrictions and supplied reflective slices.

  Literal slice domains and ambient presheaf values compute through generic
  Sigma/functor composition.  The supplied slice package retains one whole
  DefIso, so all restriction compatibility remains internal to ordinary
  transformations.  No induced topology, affine chart, or scheme is claimed.
*/

require open emdash.emdash3_2_commutative_algebra_ringed_space_restrictions;

// The restriction-oriented whole domain functor computes on literal arrows.
assert [K : Cat]
  (U V : τ (Obj K))
  (f : τ (Hom K V U)) ⊢
  @fapp0
    (@Into_restr_cat K U)
    (Op_cat K)
    (@into_restr_domain_func K U)
    (@Struct_sigma
      (Obj (Op_cat K))
      (λ X : τ (Obj (Op_cat K)),
        Obj (@Fibre_cat (Op_cat K) (@yoneda_psh K U) X))
      V f)
  ≡ V;

// Taking opposites gives the same literal computation on K/U.
assert [K : Cat]
  (U V : τ (Obj K))
  (f : τ (Hom K V U)) ⊢
  @fapp0
    (@Slice_cat K U)
    K
    (@slice_domain_func K U)
    (@Struct_sigma
      (Obj (Op_cat K))
      (λ X : τ (Obj (Op_cat K)),
        Obj (@Fibre_cat (Op_cat K) (@yoneda_psh K U) X))
      V f)
  ≡ V;

// Whole CommRing-valued pullback computes at every base object.
assert [A B : Cat]
  (F : τ (Functor A B))
  (O : τ (@CommRingPsh B))
  (a : τ (Obj A)) ⊢
  @comm_ring_psh_value A (@comm_ring_psh_pullback A B F O) a
  ≡ @comm_ring_psh_value B O (@fapp0 A B F a);

// Its arrow action is the generic structured restriction of the composite.
assert [A B : Cat]
  (F : τ (Functor A B))
  (O : τ (@CommRingPsh B))
  (x y : τ (Obj A))
  (f : τ (Hom A x y)) ⊢
  @comm_ring_psh_restriction_hom
    A (@comm_ring_psh_pullback A B F O) x y f
  : τ (@CommRingHom
      (@comm_ring_psh_value B O (@fapp0 A B F y))
      (@comm_ring_psh_value B O (@fapp0 A B F x)));

// Ambient slice values route through the whole slice-domain functor.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (q : τ (Obj (@Slice_cat K U))) ⊢
  @comm_ring_psh_value
    (@Slice_cat K U)
    (@reflective_comm_ringed_site_slice_ambient_psh K A U)
    q
  ≡ @comm_ring_psh_value
      K
      (@reflective_comm_ringed_site_underlying_psh K A)
      (@fapp0 (@Slice_cat K U) K (@slice_domain_func K U) q);

// A cover chart specializes that exact ambient restriction.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)) ⊢
  @reflective_comm_ringed_space_cover_chart_ambient_psh K P chart
  ≡ @reflective_comm_ringed_site_slice_ambient_psh
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart);

// The supplied presentation has exact constructor beta at its first field.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (B : τ (@ReflectiveCommRingedSite (@Slice_cat K U)))
  (comparison : τ (@DefIso
      (@CommRingPsh_cat (@Slice_cat K U))
      (@reflective_comm_ringed_site_underlying_psh (@Slice_cat K U) B)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U))) ⊢
  @supplied_reflective_comm_ringed_slice_ringed_site
    K A U
    (@supplied_reflective_comm_ringed_slice_intro K A U B comparison)
  ≡ B;

// Its selected topology is visibly the supplied slice site's topology.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U)) ⊢
  @supplied_reflective_comm_ringed_slice_topology K A U P
  ≡ @reflective_comm_ringed_site_topology
      (@Slice_cat K U)
      (@supplied_reflective_comm_ringed_slice_ringed_site K A U P);

// The second constructor projection returns the exact whole comparison.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (B : τ (@ReflectiveCommRingedSite (@Slice_cat K U)))
  (comparison : τ (@DefIso
      (@CommRingPsh_cat (@Slice_cat K U))
      (@reflective_comm_ringed_site_underlying_psh (@Slice_cat K U) B)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U))) ⊢
  @supplied_reflective_comm_ringed_slice_ambient_defiso
    K A U
    (@supplied_reflective_comm_ringed_slice_intro K A U B comparison)
  ≡ comparison;

// Readable components project the whole comparison; they are not new laws.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (q : τ (Obj (@Slice_cat K U))) ⊢
  @supplied_reflective_comm_ringed_slice_to_ambient_at K A U P q
  : τ (@CommRingHom
      (@comm_ring_psh_value
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
        q)
      (@comm_ring_psh_value
        K
        (@reflective_comm_ringed_site_underlying_psh K A)
        (@fapp0 (@Slice_cat K U) K (@slice_domain_func K U) q)));

assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (q : τ (Obj (@Slice_cat K U))) ⊢
  @supplied_reflective_comm_ringed_slice_from_ambient_at K A U P q
  : τ (@CommRingHom
      (@comm_ring_psh_value
        K
        (@reflective_comm_ringed_site_underlying_psh K A)
        (@fapp0 (@Slice_cat K U) K (@slice_domain_func K U) q))
      (@comm_ring_psh_value
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
        q));
