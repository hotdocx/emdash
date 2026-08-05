/*
  Internally generated Grothendieck topologies.

  A type-valued generator family may retain presentation witnesses. Generated
  coverhood is the impredicative intersection of every Grothendieck topology
  accepting those witnesses. Existing Pi/proposition owners make the
  intersection proposition-valued; topology laws are inherited pointwise.

  This transparent, rule-free module provides generator inclusion and the
  least-topology universal property. It provides no derivation syntax,
  induction on generation steps, or decision procedure for coverhood.
*/

require open emdash.emdash3_2_sites;

// Type-valued generator witnesses G(U,R) over ordinary sieves R on U.
symbol SieveGeneratorFamily
  (K : Cat)
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Pi_grpd
        (@Sieve K U)
        (λ _ : τ (@Sieve K U), Obj Grpd_cat));

// T accepts G when every retained witness in G(U,R) makes R cover in T.
symbol GrothTopologyAcceptsGenerators
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  (T : τ (@GrothTopology K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Pi_grpd
        (@Sieve K U)
        (λ R : τ (@Sieve K U),
          @Function_grpd
            (G U R)
            (@groth_topology_covers K T U R)));

// Pointwise inclusion of the proposition-valued cover predicates of T and U.
symbol GrothTopologyLe
  [K : Cat]
  (T U : τ (@GrothTopology K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ X : τ (Obj K),
      @Pi_grpd
        (@Sieve K X)
        (λ R : τ (@Sieve K X),
          @Function_grpd
            (@groth_topology_covers K T X R)
            (@groth_topology_covers K U X R)));

symbol groth_topology_le_refl
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@GrothTopologyLe K T T)
≔ λ U : τ (Obj K),
   λ R : τ (@Sieve K U),
   λ covers : τ (@groth_topology_covers K T U R), covers;

symbol groth_topology_le_trans
  [K : Cat]
  [T U V : τ (@GrothTopology K)]
  (tu : τ (@GrothTopologyLe K T U))
  (uv : τ (@GrothTopologyLe K U V))
  : τ (@GrothTopologyLe K T V)
≔ λ X : τ (Obj K),
   λ R : τ (@Sieve K X),
   λ covers : τ (@groth_topology_covers K T X R),
     uv X R (tu X R covers);

// R covers precisely when every topology accepting G declares R covering.
symbol GeneratedSieveCover
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  : Grpd
≔ @Pi_grpd
    (@GrothTopology K)
    (λ T : τ (@GrothTopology K),
      @Function_grpd
        (@GrothTopologyAcceptsGenerators K G T)
        (@groth_topology_covers K T U R));

// An intersection of proposition-valued cover predicates is a proposition.
symbol generated_sieve_cover_is_prop
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  : τ (IsPropGrpd (@GeneratedSieveCover K G U R))
≔ @is_prop_pi
    (@GrothTopology K)
    (λ T : τ (@GrothTopology K),
      @Function_grpd
        (@GrothTopologyAcceptsGenerators K G T)
        (@groth_topology_covers K T U R))
    (λ T : τ (@GrothTopology K),
      @is_prop_pi
        (@GrothTopologyAcceptsGenerators K G T)
        (λ _ : τ (@GrothTopologyAcceptsGenerators K G T),
          @groth_topology_covers K T U R)
        (λ _ : τ (@GrothTopologyAcceptsGenerators K G T),
          @covers_is_prop
            K (@groth_topology_cover_predicate K T) U R));

// The generated cover relation packaged in the existing proposition universe.
symbol generated_sieve_coverage
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@SieveCoverage K)
≔ λ U : τ (Obj K),
   λ R : τ (@Sieve K U),
     @Struct_trunc_grpd
       trunc_minus_one
       (@GeneratedSieveCover K G U R)
       (@generated_sieve_cover_is_prop K G U R);

// Maximality is inherited from every topology accepting G.
symbol generated_sieve_coverage_maximal
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@GrothMaximal K (@generated_sieve_coverage K G))
≔ λ U : τ (Obj K),
   λ T : τ (@GrothTopology K),
   λ _ : τ (@GrothTopologyAcceptsGenerators K G T),
     @groth_topology_maximal K T U;

// Pullback stability is inherited from every topology accepting G.
symbol generated_sieve_coverage_stable
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@GrothStable K (@generated_sieve_coverage K G))
≔ λ U : τ (Obj K),
   λ V : τ (Obj K),
   λ p : τ (Hom K V U),
   λ R : τ (@Sieve K U),
   λ covers : τ (@Covers K (@generated_sieve_coverage K G) U R),
   λ T : τ (@GrothTopology K),
   λ contains : τ (@GrothTopologyAcceptsGenerators K G T),
     @groth_topology_pullback K T U V p R (covers T contains);

// Local character is inherited pointwise, including every pullback premise.
symbol generated_sieve_coverage_local
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@GrothLocal K (@generated_sieve_coverage K G))
≔ λ U : τ (Obj K),
   λ R : τ (@Sieve K U),
   λ S : τ (@Sieve K U),
   λ covers : τ (@Covers K (@generated_sieve_coverage K G) U R),
   λ local : τ (@SieveLocalityPremise
      K (@generated_sieve_coverage K G) U R S),
   λ T : τ (@GrothTopology K),
   λ contains : τ (@GrothTopologyAcceptsGenerators K G T),
     @groth_topology_local_character K T U R S
       (covers T contains)
       (λ f : τ (Obj (@Into_restr_cat K U)),
        λ member : τ (@SieveMembership K U R f),
          (local f member) T contains);

symbol generated_sieve_coverage_laws
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@IsGrothTopology K (@generated_sieve_coverage K G))
≔ @Product_pair_grpd
    (@GrothMaximal K (@generated_sieve_coverage K G))
    (@Product_grpd
      (@GrothStable K (@generated_sieve_coverage K G))
      (@GrothLocal K (@generated_sieve_coverage K G)))
    (@generated_sieve_coverage_maximal K G)
    (@Product_pair_grpd
      (@GrothStable K (@generated_sieve_coverage K G))
      (@GrothLocal K (@generated_sieve_coverage K G))
      (@generated_sieve_coverage_stable K G)
      (@generated_sieve_coverage_local K G));

// The internally constructed least Grothendieck topology accepting G.
symbol generated_groth_topology
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@GrothTopology K)
≔ @groth_topology_intro
    K
    (@generated_sieve_coverage K G)
    (@generated_sieve_coverage_laws K G);

// Every retained generator covers in the generated topology.
symbol generated_groth_topology_accepts_generators
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@GrothTopologyAcceptsGenerators
      K G (@generated_groth_topology K G))
≔ λ U : τ (Obj K),
   λ R : τ (@Sieve K U),
   λ generator : τ (G U R),
   λ T : τ (@GrothTopology K),
   λ contains : τ (@GrothTopologyAcceptsGenerators K G T),
     contains U R generator;

// The generated topology is below every topology accepting G.
symbol generated_groth_topology_least
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  (T : τ (@GrothTopology K))
  (contains : τ (@GrothTopologyAcceptsGenerators K G T))
  : τ (@GrothTopologyLe K (@generated_groth_topology K G) T)
≔ λ U : τ (Obj K),
   λ R : τ (@Sieve K U),
   λ covers : τ (@groth_topology_covers
      K (@generated_groth_topology K G) U R),
     covers T contains;

// Closed nonvacuity model: the chaotic topology accepts every generator.
symbol chaotic_groth_topology_accepts_generators
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@GrothTopologyAcceptsGenerators
      K G (@chaotic_groth_topology K))
≔ λ U : τ (Obj K),
   λ R : τ (@Sieve K U),
   λ _ : τ (G U R), tt;

// Leastness therefore always has at least the chaotic comparison consumer.
symbol generated_groth_topology_le_chaotic
  [K : Cat]
  (G : τ (@SieveGeneratorFamily K))
  : τ (@GrothTopologyLe
      K (@generated_groth_topology K G) (@chaotic_groth_topology K))
≔ @generated_groth_topology_least
    K G (@chaotic_groth_topology K)
    (@chaotic_groth_topology_accepts_generators K G);
