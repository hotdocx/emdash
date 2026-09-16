/* Actual original theorem application certifies the canonical comparison at the public pair. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_middle_public_exactness;

assert [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))

 (E0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
 (E1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
 (E2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2)) (x : τ (Obj K))
 (left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (incoming_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 (outgoing_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2)) (N : τ
  (@FreydAdjunctionModelNormality R M))
 ⊢ (@freyd_native_middle_public_exact K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0
  a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain incoming_map outgoing_map N) : τ
  (@OneCatNativeExactAt (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N
  (@freyd_native_middle_public_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0
  a1 b1 d1 f0 f1 middle E0 E1 E2 x left_chain right_chain incoming_map outgoing_map));

assert [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))

 (E0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
 (E1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
 (E2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2)) (x : τ (Obj K))
 (left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (incoming_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 (outgoing_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2)) ⊢ (@fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@CommRingFreydPresentation_cat R)
  (@zero_arrow_cone_first_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_native_middle_public_input K R
  M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x
  left_chain right_chain incoming_map outgoing_map)) ≡ (@freyd_adjunction_model_object R M A0 A1 A2 a0 a1
  left_chain);
assert [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))

 (E0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
 (E1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
 (E2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2)) (x : τ (Obj K))
 (left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (incoming_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 (outgoing_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2)) ⊢
  (@terminal_arrow_test_outgoing (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_native_middle_public_input K R
  M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 x
  left_chain right_chain incoming_map outgoing_map))) ≡ (@freyd_adjunction_model_map R M B0 B1 B2 D0 D1 D2
  b0 b1 d0 d1 p0 p1 p2 middle right_chain outgoing_map);
