/*
  Reviewer-facing internally generated Grothendieck topologies.
*/

require open emdash.emdash3_2_generated_topologies;

// Any proposition-valued coverage can be viewed as a type-valued generator.
symbol coverage_sieve_generators
  [K : Cat]
  (C : τ (@SieveCoverage K))
  : τ (@SieveGeneratorFamily K)
≔ λ U : τ (Obj K),
   λ R : τ (@Sieve K U), @Covers K C U R;

// catalog-area: Internally generated Grothendieck topologies
// Formation of the generated proposition-valued coverage.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K)) ⊢
  @generated_sieve_coverage K G
  : τ (@SieveCoverage K);

// The selected coverage carries all three Grothendieck laws.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K)) ⊢
  @generated_sieve_coverage_laws K G
  : τ (@IsGrothTopology K (@generated_sieve_coverage K G));

// Formation of the internally constructed topology.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K)) ⊢
  @generated_groth_topology K G
  : τ (@GrothTopology K);

// Every retained witness is accepted by the generated topology.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  (generator : τ (G U R)) ⊢
  @generated_groth_topology_accepts_generators K G U R generator
  : τ (@groth_topology_covers
      K (@generated_groth_topology K G) U R);

// Generator inclusion computes to the supplied accepting-topology witness.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  (generator : τ (G U R))
  (T : τ (@GrothTopology K))
  (contains : τ (@GrothTopologyAcceptsGenerators K G T)) ⊢
  (@generated_groth_topology_accepts_generators K G U R generator)
    T contains
  ≡ contains U R generator;

// Leastness eliminates every generated cover into an accepting topology.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  (T : τ (@GrothTopology K))
  (contains : τ (@GrothTopologyAcceptsGenerators K G T))
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  (covers : τ (@groth_topology_covers
      K (@generated_groth_topology K G) U R)) ⊢
  (@generated_groth_topology_least K G T contains) U R covers
  : τ (@groth_topology_covers K T U R);

// Leastness computes by evaluating a generated-cover witness at T.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  (T : τ (@GrothTopology K))
  (contains : τ (@GrothTopologyAcceptsGenerators K G T))
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  (covers : τ (@groth_topology_covers
      K (@generated_groth_topology K G) U R)) ⊢
  (@generated_groth_topology_least K G T contains) U R covers
  ≡ covers T contains;

// The chaotic topology is a closed accepting upper bound for every G.
assert [K : Cat]
  (G : τ (@SieveGeneratorFamily K)) ⊢
  @chaotic_groth_topology_accepts_generators K G
  : τ (@GrothTopologyAcceptsGenerators
      K G (@chaotic_groth_topology K));

// Coverage witnesses specialize without reflection or witness erasure.
assert [K : Cat]
  (C : τ (@SieveCoverage K))
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  (generator : τ (@Covers K C U R)) ⊢
  @generated_groth_topology_accepts_generators
    K (@coverage_sieve_generators K C) U R generator
  : τ (@groth_topology_covers
      K
      (@generated_groth_topology K (@coverage_sieve_generators K C))
      U R);
