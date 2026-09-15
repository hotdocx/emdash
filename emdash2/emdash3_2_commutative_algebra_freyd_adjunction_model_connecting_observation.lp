/* Direct native row contracts and complete-arrow observation of whole δ.
   The concrete CAS interface uses Terminal as its index; native whole owners
   retain their general base and action. No legacy H comparison is involved. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_short_exact;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;
require open emdash.emdash3_2_commutative_algebra_freyd_raw_window_connecting_observation;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_observations;
require open emdash.emdash3_2_commutative_algebra_freyd_arrow_observations;

// Original whole P/Q shortness at the original constant raw row.
symbol FreydAdjunctionModelRowShortExact [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) : Grpd
≔ @FreydRawNativeRowShortExact Terminal_cat R M A B D e d chain;

// Complete-arrow observation of the original whole native δ.
symbol freyd_adjunction_model_connecting_observation [R : τ CommRing]
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
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_object R M Dm D0 D1 dm d0 source_chain)
  (@freyd_adjunction_model_object R M A0 A1 A2 a0 a1 target_chain) (@freyd_raw_native_window_connecting_at Terminal_cat R M N
  Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1
  b1 d1 jm upper lower source_chain target_chain Terminal_obj);
