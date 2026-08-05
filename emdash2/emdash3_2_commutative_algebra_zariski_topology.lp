/*
  Supplied Grothendieck topologies compatible with selected Zariski covers.

  A compatibility witness says that every ordinary sieve containing all
  basic-open arrows of a selected finite Zariski presentation covers in an
  already supplied topology on `Op_cat CommRing_cat`.  The presentation,
  localization packages, and membership terms remain explicit computational
  data; only the resulting coverhood is proposition-valued.

  This rule-free one-way module does not construct the least/generated
  Zariski topology, identify different presentations, choose localizations,
  or add propositional truncation, sheafification, subcanonicity, `Spec`, or
  schemes.  The chaotic model witnesses feasibility, not exactness or
  minimality of the selected topology.
*/

require open emdash.emdash3_2_commutative_algebra_zariski;

// Every sieve containing this selected presentation covers in T.
symbol CommRingZariskiPresentationCovers
  (T : τ (@GrothTopology (Op_cat CommRing_cat)))
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  : Grpd
≔ @Pi_grpd
    (@Sieve (Op_cat CommRing_cat) R)
    (λ Q : τ (@Sieve (Op_cat CommRing_cat) R),
      @Function_grpd
        (@CommRingZariskiCoverFamilyMembership R family Q)
        (@groth_topology_covers
          (Op_cat CommRing_cat) T R Q));

// T admits every selected finite Zariski basic-open presentation.
symbol IsCommRingZariskiCompatibleTopology
  (T : τ (@GrothTopology (Op_cat CommRing_cat)))
  : Grpd
≔ @Pi_grpd
    CommRing
    (λ R : τ CommRing,
      @Pi_grpd
        (@CommRingZariskiCoverFamily R)
        (λ family : τ (@CommRingZariskiCoverFamily R),
          @CommRingZariskiPresentationCovers T R family));

// Presentation coverhood is proposition-valued without truncating its data.
symbol comm_ring_zariski_presentation_covers_is_prop
  (T : τ (@GrothTopology (Op_cat CommRing_cat)))
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  : τ (IsPropGrpd (@CommRingZariskiPresentationCovers T R family))
≔ @is_prop_pi
    (@Sieve (Op_cat CommRing_cat) R)
    (λ Q : τ (@Sieve (Op_cat CommRing_cat) R),
      @Function_grpd
        (@CommRingZariskiCoverFamilyMembership R family Q)
        (@groth_topology_covers
          (Op_cat CommRing_cat) T R Q))
    (λ Q : τ (@Sieve (Op_cat CommRing_cat) R),
      @is_prop_pi
        (@CommRingZariskiCoverFamilyMembership R family Q)
        (λ _ : τ (@CommRingZariskiCoverFamilyMembership R family Q),
          @groth_topology_covers
            (Op_cat CommRing_cat) T R Q)
        (λ _ : τ (@CommRingZariskiCoverFamilyMembership R family Q),
          @covers_is_prop
            (Op_cat CommRing_cat)
            (@groth_topology_cover_predicate
              (Op_cat CommRing_cat) T)
            R Q));

// Compatibility itself is a property of the supplied topology.
symbol is_comm_ring_zariski_compatible_topology_is_prop
  (T : τ (@GrothTopology (Op_cat CommRing_cat)))
  : τ (IsPropGrpd (@IsCommRingZariskiCompatibleTopology T))
≔ @is_prop_pi
    CommRing
    (λ R : τ CommRing,
      @Pi_grpd
        (@CommRingZariskiCoverFamily R)
        (λ family : τ (@CommRingZariskiCoverFamily R),
          @CommRingZariskiPresentationCovers T R family))
    (λ R : τ CommRing,
      @is_prop_pi
        (@CommRingZariskiCoverFamily R)
        (λ family : τ (@CommRingZariskiCoverFamily R),
          @CommRingZariskiPresentationCovers T R family)
        (λ family : τ (@CommRingZariskiCoverFamily R),
          @comm_ring_zariski_presentation_covers_is_prop T R family));

// Evidence-retaining package: a supplied topology plus compatibility proof.
symbol CommRingZariskiCompatibleTopology : Grpd
≔ `Σ_ T : τ (@GrothTopology (Op_cat CommRing_cat)),
     @IsCommRingZariskiCompatibleTopology T;

symbol comm_ring_zariski_compatible_topology_intro
  (T : τ (@GrothTopology (Op_cat CommRing_cat)))
  (compatible : τ (@IsCommRingZariskiCompatibleTopology T))
  : τ CommRingZariskiCompatibleTopology
≔ @Struct_sigma
    (@GrothTopology (Op_cat CommRing_cat))
    (λ T0 : τ (@GrothTopology (Op_cat CommRing_cat)),
      @IsCommRingZariskiCompatibleTopology T0)
    T compatible;

symbol comm_ring_zariski_compatible_topology_topology
  (ZT : τ CommRingZariskiCompatibleTopology)
  : τ (@GrothTopology (Op_cat CommRing_cat))
≔ sigma_Fst ZT;

symbol comm_ring_zariski_compatible_topology_compatible
  (ZT : τ CommRingZariskiCompatibleTopology)
  : τ (@IsCommRingZariskiCompatibleTopology
      (@comm_ring_zariski_compatible_topology_topology ZT))
≔ sigma_Snd ZT;

// Convert explicit selected containment into proposition-valued coverhood.
symbol comm_ring_zariski_compatible_topology_covers
  (ZT : τ CommRingZariskiCompatibleTopology)
  [R : τ CommRing]
  (family : τ (@CommRingZariskiCoverFamily R))
  (Q : τ (@Sieve (Op_cat CommRing_cat) R))
  (members : τ (@CommRingZariskiCoverFamilyMembership R family Q))
  : τ (@groth_topology_covers
      (Op_cat CommRing_cat)
      (@comm_ring_zariski_compatible_topology_topology ZT)
      R Q)
≔ (@comm_ring_zariski_compatible_topology_compatible ZT)
    R family Q members;

// Closed feasibility model: every sieve covers in the chaotic topology.
symbol chaotic_is_comm_ring_zariski_compatible
  : τ (@IsCommRingZariskiCompatibleTopology
      (@chaotic_groth_topology (Op_cat CommRing_cat)))
≔ λ R : τ CommRing,
    λ family : τ (@CommRingZariskiCoverFamily R),
    λ Q : τ (@Sieve (Op_cat CommRing_cat) R),
    λ _ : τ (@CommRingZariskiCoverFamilyMembership R family Q),
      tt;

symbol chaotic_comm_ring_zariski_compatible_topology
  : τ CommRingZariskiCompatibleTopology
≔ @comm_ring_zariski_compatible_topology_intro
    (@chaotic_groth_topology (Op_cat CommRing_cat))
    chaotic_is_comm_ring_zariski_compatible;
