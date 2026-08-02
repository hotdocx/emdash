/*
  Reviewer for a supplied topology compatible with selected finite Zariski
  presentations.

  Compatibility turns explicit family containment into proposition-valued
  coverhood in an already lawful topology.  It does not construct a generated
  topology or truncate the retained presentation/localization data.
*/

require open emdash.emdash3_2_commutative_algebra_zariski_topology;

assert [T : τ (@GrothTopology (Op_cat CommRing_cat))]
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R)) ⊢
  @CommRingZariskiPresentationCovers T R family
  : Grpd;

assert [T : τ (@GrothTopology (Op_cat CommRing_cat))]
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R)) ⊢
  @comm_ring_zariski_presentation_covers_is_prop T R family
  : τ (IsPropGrpd (@CommRingZariskiPresentationCovers T R family));

assert [T : τ (@GrothTopology (Op_cat CommRing_cat))] ⊢
  @is_comm_ring_zariski_compatible_topology_is_prop T
  : τ (IsPropGrpd (@IsCommRingZariskiCompatibleTopology T));

assert [T : τ (@GrothTopology (Op_cat CommRing_cat))]
  (compatible : τ (@IsCommRingZariskiCompatibleTopology T)) ⊢
  @comm_ring_zariski_compatible_topology_topology
    (@comm_ring_zariski_compatible_topology_intro T compatible)
  ≡ T;

assert [T : τ (@GrothTopology (Op_cat CommRing_cat))]
  (compatible : τ (@IsCommRingZariskiCompatibleTopology T)) ⊢
  @comm_ring_zariski_compatible_topology_compatible
    (@comm_ring_zariski_compatible_topology_intro T compatible)
  ≡ compatible;

assert ⊢
  chaotic_comm_ring_zariski_compatible_topology
  : τ CommRingZariskiCompatibleTopology;

assert ⊢
  @comm_ring_zariski_compatible_topology_topology
    chaotic_comm_ring_zariski_compatible_topology
  ≡ @chaotic_groth_topology (Op_cat CommRing_cat);

assert [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (members : τ (@CommRingZariskiCoverFamilyMembership R family Q)) ⊢
  @comm_ring_zariski_compatible_topology_covers
    chaotic_comm_ring_zariski_compatible_topology
    R family Q members
  ≡ tt;
