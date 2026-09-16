/* Terminal-indexed frontend views of the original public native inputs and certificates. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_middle_pair_exactness;
require open emdash.emdash3_2_commutative_algebra_freyd_native_diagram_exactness;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_row_context;
require open emdash.emdash3_2_commutative_algebra_freyd_native_source_pair_exactness;
require open emdash.emdash3_2_commutative_algebra_freyd_native_target_pair_exactness;

// Retain the original middle native input at the frontend's Terminal index.
symbol freyd_native_model_middle_pair_input  [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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

 (E0 : τ (@FreydAdjunctionModelRowShortExact R M A0 B0 D0 i0 p0 c0))
 (E1 : τ (@FreydAdjunctionModelRowShortExact R M A1 B1 D1 i1 p1 c1))
 (E2 : τ (@FreydAdjunctionModelRowShortExact R M A2 B2 D2 i2 p2 c2))
 (left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (incoming_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 (outgoing_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2)) (N : τ
  (@FreydAdjunctionModelNormality R M))
 : τ (FreydNativeInput R)
≔ (@freyd_native_middle_public_input Terminal_cat R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2
  a0 b0 d0
  a1 b1 d1 f0 f1 middle E0 E1 E2 Terminal_obj left_chain right_chain incoming_map outgoing_map);

// Apply the original certificate constructor with the same model and interpretation paths.
symbol freyd_native_model_middle_pair_exact_at  [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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

 (E0 : τ (@FreydAdjunctionModelRowShortExact R M A0 B0 D0 i0 p0 c0))
 (E1 : τ (@FreydAdjunctionModelRowShortExact R M A1 B1 D1 i1 p1 c1))
 (E2 : τ (@FreydAdjunctionModelRowShortExact R M A2 B2 D2 i2 p2 c2))
 (left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (incoming_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 (outgoing_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2)) (N : τ
  (@FreydAdjunctionModelNormality R M))
 [edge0 edge1 : τ (FreydArrowObservation R)]
 (p : τ (@= (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R)
  (@freyd_adjunction_model_object R M A0
  A1 A2 a0 a1 left_chain) (@freyd_adjunction_model_object R M B0 B1 B2 b0 b1 middle)
  (@freyd_adjunction_model_map R M A0 A1
  A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2 left_chain middle incoming_map)) edge0))
 (q : τ (@= (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R)
  (@freyd_adjunction_model_object R M B0 B1 B2 b0 b1 middle) (@freyd_adjunction_model_object R M D0 D1 D2 d0
  d1 right_chain) (@freyd_adjunction_model_map R M B0 B1
  B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2 middle right_chain outgoing_map)) edge1))
 : τ (@FreydNativeObservedPairExactAt R M N (@freyd_native_model_middle_pair_input R M A0 B0 D0 A1 B1 D1 A2
  B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 left_chain right_chain
  incoming_map outgoing_map N) edge0 edge1)
≔ @freyd_native_middle_public_pair_exact_at Terminal_cat R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0
  c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 E1 E2 Terminal_obj left_chain right_chain incoming_map
  outgoing_map N edge0 edge1 p q;

// Retain the original source native input at the frontend's Terminal index.
symbol freyd_native_model_source_pair_input  [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydAdjunctionModelRowShortExact R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydAdjunctionModelRowShortExact R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydAdjunctionModelRowShortExact R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydAdjunctionModelRowShortExact R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
 (source_chain : τ (@CommRingFreydChainPair R Dm D0 D1 dm d0))
 (target_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (unused_left_chain : τ (@CommRingFreydChainPair R Am A0 A1 am a0))
 (column_map : τ (@CommRingFreydHomologyChainMap R Bm B0 B1 Dm D0 D1 bm b0 dm d0 pm p0 p1))
 : τ (FreydNativeInput R)
≔ (@freyd_native_source_public_input Terminal_cat R M N Am Bm Dm A0 B0 D0
  A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm
  upper lower source_chain target_chain Terminal_obj unused_left_chain column_map);

// Apply the original certificate constructor with the same model and interpretation paths.
symbol freyd_native_model_source_pair_exact_at  [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydAdjunctionModelRowShortExact R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydAdjunctionModelRowShortExact R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydAdjunctionModelRowShortExact R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydAdjunctionModelRowShortExact R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
 (source_chain : τ (@CommRingFreydChainPair R Dm D0 D1 dm d0))
 (target_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (unused_left_chain : τ (@CommRingFreydChainPair R Am A0 A1 am a0))
 (column_map : τ (@CommRingFreydHomologyChainMap R Bm B0 B1 Dm D0 D1 bm b0 dm d0 pm p0 p1))
 [edge0 edge1 : τ (FreydArrowObservation R)]
 (p : τ (@= (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R)
  (@freyd_adjunction_model_object R M Bm B0 B1 bm b0 upper) (@freyd_adjunction_model_object R M Dm D0 D1 dm
  d0 source_chain) (@freyd_adjunction_model_map R M Bm B0 B1 Dm D0 D1 bm b0 dm d0 pm p0 p1 upper
  source_chain column_map)) edge0))
 (q : τ (@= (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R)
  (@freyd_adjunction_model_object R M Dm D0 D1 dm d0 source_chain) (@freyd_adjunction_model_object R M A0
  A1 A2 a0 a1 target_chain) (@freyd_raw_native_window_connecting_at Terminal_cat R M N Am Bm Dm A0 B0 D0 A1
  B1 D1 A2
  B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower
  source_chain target_chain Terminal_obj)) edge1))
 : τ (@FreydNativeObservedPairExactAt R M N (@freyd_native_model_source_pair_input R M N Am Bm Dm A0 B0 D0
  A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm
  upper lower source_chain target_chain unused_left_chain column_map) edge0 edge1)
≔ @freyd_native_source_public_pair_exact_at Terminal_cat R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm
  xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower source_chain
  target_chain Terminal_obj unused_left_chain column_map edge0 edge1 p q;

// Retain the original target native input at the frontend's Terminal index.
symbol freyd_native_model_target_pair_input  [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydAdjunctionModelRowShortExact R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydAdjunctionModelRowShortExact R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydAdjunctionModelRowShortExact R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydAdjunctionModelRowShortExact R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
 (source_chain : τ (@CommRingFreydChainPair R Dm D0 D1 dm d0))
 (target_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (bottom_right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (column_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 : τ (FreydNativeInput R)
≔ (@freyd_native_target_public_input Terminal_cat R M N Am Bm Dm A0 B0 D0
  A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm
  upper lower source_chain target_chain Terminal_obj bottom_right_chain column_map);

// Apply the original certificate constructor with the same model and interpretation paths.
symbol freyd_native_model_target_pair_exact_at  [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydAdjunctionModelRowShortExact R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydAdjunctionModelRowShortExact R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydAdjunctionModelRowShortExact R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydAdjunctionModelRowShortExact R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
 (source_chain : τ (@CommRingFreydChainPair R Dm D0 D1 dm d0))
 (target_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (bottom_right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (column_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 [edge0 edge1 : τ (FreydArrowObservation R)]
 (p : τ (@= (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R)
  (@freyd_adjunction_model_object R M Dm D0 D1 dm d0 source_chain) (@freyd_adjunction_model_object R M A0 A1
  A2 a0 a1 target_chain) (@freyd_raw_native_window_connecting_at Terminal_cat R M N Am Bm Dm A0 B0 D0 A1 B1
  D1 A2 B2 D2
  im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower
  source_chain target_chain Terminal_obj)) edge0))
 (q : τ (@= (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R)
  (@freyd_adjunction_model_object R M A0 A1 A2 a0 a1 target_chain) (@freyd_adjunction_model_object R M B0
  B1 B2 b0 b1 lower) (@freyd_adjunction_model_map R M A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2
  target_chain lower column_map)) edge1))
 : τ (@FreydNativeObservedPairExactAt R M N (@freyd_native_model_target_pair_input R M N Am Bm Dm A0 B0 D0
  A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm
  upper lower source_chain target_chain bottom_right_chain column_map) edge0 edge1)
≔ @freyd_native_target_public_pair_exact_at Terminal_cat R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm
  xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower source_chain
  target_chain Terminal_obj bottom_right_chain column_map edge0 edge1 p q;
