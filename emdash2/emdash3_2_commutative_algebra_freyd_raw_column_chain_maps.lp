/* Column chain maps derived from the original row-map agreements. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_maps;
require open emdash.emdash3_2_commutative_algebra_presentation_agreement_operations;

// The two original row squares, in the column orientation.
symbol freyd_raw_column_incoming_chain_map  [R : τ CommRing]
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]



  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))


 : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2)
≔ Struct_sigma (@comm_ring_presentation_agreement_sym R A0 B1 (@comm_ring_presentation_morphism_map R A0
  B1 (@comm_ring_presentation_morphism_comp R A0 A1 B1 i1 a0)) (@comm_ring_presentation_morphism_map R A0
  B1 (@comm_ring_presentation_morphism_comp R A0 B0 B1 b0 i0)) (@comm_ring_freyd_homology_chain_map_upper
  R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 f0)) (@comm_ring_presentation_agreement_sym R A1 B2
  (@comm_ring_presentation_morphism_map R A1 B2 (@comm_ring_presentation_morphism_comp R A1 A2 B2 i2 a1))
  (@comm_ring_presentation_morphism_map R A1 B2 (@comm_ring_presentation_morphism_comp R A1 B1 B2 b1 i1))
  (@comm_ring_freyd_homology_chain_map_upper R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 f1));

// The two original row squares, in the column orientation.
symbol freyd_raw_column_outgoing_chain_map  [R : τ CommRing]
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]



  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))


 : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2)
≔ Struct_sigma (@comm_ring_presentation_agreement_sym R B0 D1 (@comm_ring_presentation_morphism_map R B0
  D1 (@comm_ring_presentation_morphism_comp R B0 B1 D1 p1 b0)) (@comm_ring_presentation_morphism_map R B0
  D1 (@comm_ring_presentation_morphism_comp R B0 D0 D1 d0 p0)) (@comm_ring_freyd_homology_chain_map_lower
  R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 f0)) (@comm_ring_presentation_agreement_sym R B1 D2
  (@comm_ring_presentation_morphism_map R B1 D2 (@comm_ring_presentation_morphism_comp R B1 B2 D2 p2 b1))
  (@comm_ring_presentation_morphism_map R B1 D2 (@comm_ring_presentation_morphism_comp R B1 D1 D2 d1 p1))
  (@comm_ring_freyd_homology_chain_map_lower R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 f1));
