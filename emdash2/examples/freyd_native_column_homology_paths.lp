/* Middle comparison uses the original middle chain, with no short-exact-row premise. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_column_homology_paths;
require open emdash.emdash3_2_commutative_algebra_freyd_raw_column_chain_maps;
require open emdash.emdash3_2_one_cat_row_homology_maps;
symbol K : Cat;
symbol R : τ CommRing;
symbol M : τ (FreydAdjunctionModel R);
symbol A0 : τ (@CommRingPresentation R);
symbol B0 : τ (@CommRingPresentation R);
symbol D0 : τ (@CommRingPresentation R);
symbol A1 : τ (@CommRingPresentation R);
symbol B1 : τ (@CommRingPresentation R);
symbol D1 : τ (@CommRingPresentation R);
symbol A2 : τ (@CommRingPresentation R);
symbol B2 : τ (@CommRingPresentation R);
symbol D2 : τ (@CommRingPresentation R);
symbol i0 : τ (@CommRingPresentationMorphism R A0 B0);
symbol p0 : τ (@CommRingPresentationMorphism R B0 D0);
symbol i1 : τ (@CommRingPresentationMorphism R A1 B1);
symbol p1 : τ (@CommRingPresentationMorphism R B1 D1);
symbol i2 : τ (@CommRingPresentationMorphism R A2 B2);
symbol p2 : τ (@CommRingPresentationMorphism R B2 D2);
symbol c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0);
symbol c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1);
symbol c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2);
symbol a0 : τ (@CommRingPresentationMorphism R A0 A1);
symbol b0 : τ (@CommRingPresentationMorphism R B0 B1);
symbol d0 : τ (@CommRingPresentationMorphism R D0 D1);
symbol a1 : τ (@CommRingPresentationMorphism R A1 A2);
symbol b1 : τ (@CommRingPresentationMorphism R B1 B2);
symbol d1 : τ (@CommRingPresentationMorphism R D1 D2);
symbol f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0);
symbol f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1);
symbol middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1);
symbol x : τ (Obj K);

symbol E0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0);
symbol E1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1);
symbol E2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2);
symbol left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1);
symbol right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1);
symbol incoming_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2);
symbol outgoing_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2);

// Original row agreements mechanically construct the corresponding column map.
symbol derived_incoming_map ≔ @freyd_raw_column_incoming_chain_map R A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 f0 f1;
assert ⊢ derived_incoming_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2);
// Both supplied CAS map evidence and the derived evidence consume the actual theorem.
symbol incoming_diagram_agreement ≔ @freyd_native_column_incoming_diagram_path K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain incoming_map;
symbol incoming_H_agreement ≔ @freyd_native_column_incoming_homology_path K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain incoming_map;
symbol derived_incoming_H_agreement ≔ @freyd_native_column_incoming_homology_path K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain derived_incoming_map;

// Original row agreements mechanically construct the corresponding column map.
symbol derived_outgoing_map ≔ @freyd_raw_column_outgoing_chain_map R A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 f0 f1;
assert ⊢ derived_outgoing_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2);
// Both supplied CAS map evidence and the derived evidence consume the actual theorem.
symbol outgoing_diagram_agreement ≔ @freyd_native_column_outgoing_diagram_path K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain outgoing_map;
symbol outgoing_H_agreement ≔ @freyd_native_column_outgoing_homology_path K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain outgoing_map;
symbol derived_outgoing_H_agreement ≔ @freyd_native_column_outgoing_homology_path K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain derived_outgoing_map;
