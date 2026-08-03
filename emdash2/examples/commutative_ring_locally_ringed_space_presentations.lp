/*
  Reviewer for topology-local whole-object and binary affine-cover
  presentations.

  Local-ring computation is retained on the whole ambient restriction over
  K/X, while the supplied reflective slice owns sheaf semantics and its whole
  DefIso.  The combined package deliberately remains short of a scheme claim.
*/

require open emdash.emdash3_2_commutative_algebra_locally_ringed_space_presentations;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K)) ⊢
  @ReflectiveCommRingedWholeObjectLocalPresentation K P : Grpd;

// The whole-object constructor retains the exact supplied reflective slice.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (S : τ (@SuppliedReflectiveCommRingedSlicePresentation
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_whole_object K P)))
  (local : τ (@CommRingPshTopologyLocalRingPresentation
      (@Slice_cat K
        (@reflective_comm_ringed_space_cover_whole_object K P))
      (@supplied_reflective_comm_ringed_slice_topology
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)
        S)
      (@reflective_comm_ringed_site_slice_ambient_psh
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)))) ⊢
  @reflective_comm_ringed_whole_object_local_slice
    K P
    (@reflective_comm_ringed_whole_object_local_intro K P S local)
  ≡ S;

// Its local-ring computation is the second transparent field.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (S : τ (@SuppliedReflectiveCommRingedSlicePresentation
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_whole_object K P)))
  (local : τ (@CommRingPshTopologyLocalRingPresentation
      (@Slice_cat K
        (@reflective_comm_ringed_space_cover_whole_object K P))
      (@supplied_reflective_comm_ringed_slice_topology
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)
        S)
      (@reflective_comm_ringed_site_slice_ambient_psh
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)))) ⊢
  @reflective_comm_ringed_whole_object_local_ring
    K P
    (@reflective_comm_ringed_whole_object_local_intro K P S local)
  ≡ local;

// The readable topology and presheaf remain routed through existing owners.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P)) ⊢
  @reflective_comm_ringed_whole_object_local_topology K P L
  ≡ @supplied_reflective_comm_ringed_slice_topology
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (sigma_Fst L);

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P)) ⊢
  @reflective_comm_ringed_whole_object_local_psh K P L
  ≡ @reflective_comm_ringed_site_slice_ambient_psh
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_whole_object K P);

// The sheaf/computing comparison is the supplied whole DefIso, not a new
// component equation.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P)) ⊢
  @reflective_comm_ringed_whole_object_local_ambient_defiso K P L
  ≡ @supplied_reflective_comm_ringed_slice_ambient_defiso
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (sigma_Fst L);

// The final conservative package transparently retains local and atlas data.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (local : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  (atlas : τ (@BinaryAffineCoverPresentation K P)) ⊢
  @binary_locally_ringed_affine_cover_local
    K P
    (@binary_locally_ringed_affine_cover_intro K P local atlas)
  ≡ local;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (local : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  (atlas : τ (@BinaryAffineCoverPresentation K P)) ⊢
  @binary_locally_ringed_affine_cover_atlas
    K P
    (@binary_locally_ringed_affine_cover_intro K P local atlas)
  ≡ atlas;
