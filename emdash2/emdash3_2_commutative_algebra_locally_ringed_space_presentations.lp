/*
  Topology-local whole-object and affine-cover presentations.

  A distinguished object X of an ambient reflective CommRinged site is
  presented on its actual slice K/X.  The existing supplied reflective-slice
  package owns that slice's topology, sheafification boundary, structure
  sheaf, and one whole DefIso to the computing ambient restriction.  The
  topology-local local-ring capability is attached to that computing target,
  so sections, restrictions, unit tests, selected covers, and Boolean local
  branches retain their existing executable owners.

  Pairing this whole-object presentation with the existing globally generated
  binary affine cover yields a locally-ringed affine-cover presentation.  The
  name deliberately stops short of `SchemePresentation`: on an arbitrary
  Grothendieck site a covering-sieve member need not be an open immersion, and
  no admissible-open or relative-geometry class is currently retained.  This
  transparent module adds no rule, unifier, external coherence field, overlap
  field, cocycle field, gluing constructor, or category of schemes.
*/

require open emdash.emdash3_2_commutative_algebra_local_ringed_sites;
require open emdash.emdash3_2_commutative_algebra_affine_cover_presentations;

/*
  A computing topology-local presentation of the whole object X.

  S supplies reflective semantics on K/X and a whole DefIso from its included
  sheaf to the ambient restriction.  Local-ring computation runs on the
  latter, not on an unrelated or object-only replacement.
*/
symbol ReflectiveCommRingedWholeObjectLocalPresentation
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : Grpd
≔ `Σ_ S : τ (@SuppliedReflectiveCommRingedSlicePresentation
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)),
      @CommRingPshTopologyLocalRingPresentation
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
          (@reflective_comm_ringed_space_cover_whole_object K P));

symbol reflective_comm_ringed_whole_object_local_intro
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
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
        (@reflective_comm_ringed_space_cover_whole_object K P))))
  : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P)
≔ @Struct_sigma
    (@SuppliedReflectiveCommRingedSlicePresentation
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_whole_object K P))
    (λ S0 : τ (@SuppliedReflectiveCommRingedSlicePresentation
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)),
      @CommRingPshTopologyLocalRingPresentation
        (@Slice_cat K
          (@reflective_comm_ringed_space_cover_whole_object K P))
        (@supplied_reflective_comm_ringed_slice_topology
          K
          (@reflective_comm_ringed_space_cover_ringed_site K P)
          (@reflective_comm_ringed_space_cover_whole_object K P)
          S0)
        (@reflective_comm_ringed_site_slice_ambient_psh
          K
          (@reflective_comm_ringed_space_cover_ringed_site K P)
          (@reflective_comm_ringed_space_cover_whole_object K P)))
    S local;

// Supplied reflective slice of the distinguished whole object.
symbol reflective_comm_ringed_whole_object_local_slice
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  : τ (@SuppliedReflectiveCommRingedSlicePresentation
      K
      (@reflective_comm_ringed_space_cover_ringed_site K P)
      (@reflective_comm_ringed_space_cover_whole_object K P))
≔ sigma_Fst L;

// Selected whole-object slice topology; no induced-topology claim is added.
symbol reflective_comm_ringed_whole_object_local_topology
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  : τ (@GrothTopology (@Slice_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))
≔ @supplied_reflective_comm_ringed_slice_topology
    K
    (@reflective_comm_ringed_space_cover_ringed_site K P)
    (@reflective_comm_ringed_space_cover_whole_object K P)
    (sigma_Fst L);

// Computing ambient structure presheaf on K/X.
symbol reflective_comm_ringed_whole_object_local_psh
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  : τ (@CommRingPsh (@Slice_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))
≔ @reflective_comm_ringed_site_slice_ambient_psh
    K
    (@reflective_comm_ringed_space_cover_ringed_site K P)
    (@reflective_comm_ringed_space_cover_whole_object K P);

// Whole DefIso from the supplied included sheaf to that computing presheaf.
symbol reflective_comm_ringed_whole_object_local_ambient_defiso
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  : τ (@DefIso
      (@CommRingPsh_cat (@Slice_cat K
        (@reflective_comm_ringed_space_cover_whole_object K P)))
      (@supplied_reflective_comm_ringed_slice_underlying_psh
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)
        (sigma_Fst L))
      (@reflective_comm_ringed_site_slice_ambient_psh
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)))
≔ @supplied_reflective_comm_ringed_slice_ambient_defiso
    K
    (@reflective_comm_ringed_space_cover_ringed_site K P)
    (@reflective_comm_ringed_space_cover_whole_object K P)
    (sigma_Fst L);

// Retained topology-local computation on the literal nested-Sigma endpoint.
symbol reflective_comm_ringed_whole_object_local_ring
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (L : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  : τ (@CommRingPshTopologyLocalRingPresentation
      (@Slice_cat K
        (@reflective_comm_ringed_space_cover_whole_object K P))
      (@supplied_reflective_comm_ringed_slice_topology
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)
        (sigma_Fst L))
      (@reflective_comm_ringed_site_slice_ambient_psh
        K
        (@reflective_comm_ringed_space_cover_ringed_site K P)
        (@reflective_comm_ringed_space_cover_whole_object K P)))
≔ sigma_Snd L;

/*
  Locally-ringed binary affine-cover presentation.

  This is the completed local-support plus atlas package, but it is not yet
  promoted to the representation-independent semantic name `Scheme`.
*/
symbol BinaryLocallyRingedAffineCoverPresentation
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : Grpd
≔ `Σ_ local : τ (@ReflectiveCommRingedWholeObjectLocalPresentation
        K P),
      @BinaryAffineCoverPresentation K P;

symbol binary_locally_ringed_affine_cover_intro
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (local : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  (atlas : τ (@BinaryAffineCoverPresentation K P))
  : τ (@BinaryLocallyRingedAffineCoverPresentation K P)
≔ @Struct_sigma
    (@ReflectiveCommRingedWholeObjectLocalPresentation K P)
    (λ _ : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P),
      @BinaryAffineCoverPresentation K P)
    local atlas;

symbol binary_locally_ringed_affine_cover_local
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P))
  : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P)
≔ sigma_Fst Q;

symbol binary_locally_ringed_affine_cover_atlas
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P))
  : τ (@BinaryAffineCoverPresentation K P)
≔ sigma_Snd Q;
