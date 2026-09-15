/* Whole categorical exactness: original predicates and derived evidence. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_exactness_observations;

symbol K : Cat;
symbol R : τ CommRing;
symbol M : τ (FreydAdjunctionModel R);
symbol N : τ (@FreydAdjunctionModelNormality R M);
symbol Am : τ (@CommRingPresentation R);
symbol Bm : τ (@CommRingPresentation R);
symbol Dm : τ (@CommRingPresentation R);
symbol A0 : τ (@CommRingPresentation R);
symbol B0 : τ (@CommRingPresentation R);
symbol D0 : τ (@CommRingPresentation R);
symbol A1 : τ (@CommRingPresentation R);
symbol B1 : τ (@CommRingPresentation R);
symbol D1 : τ (@CommRingPresentation R);
symbol A2 : τ (@CommRingPresentation R);
symbol B2 : τ (@CommRingPresentation R);
symbol D2 : τ (@CommRingPresentation R);
symbol im : τ (@CommRingPresentationMorphism R Am Bm);
symbol pm : τ (@CommRingPresentationMorphism R Bm Dm);
symbol cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm);
symbol xm : τ (@FreydRawNativeRowShortExact K R M Am Bm Dm im pm cm);
symbol i0 : τ (@CommRingPresentationMorphism R A0 B0);
symbol p0 : τ (@CommRingPresentationMorphism R B0 D0);
symbol c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0);
symbol x0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0);
symbol i1 : τ (@CommRingPresentationMorphism R A1 B1);
symbol p1 : τ (@CommRingPresentationMorphism R B1 D1);
symbol c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1);
symbol x1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1);
symbol i2 : τ (@CommRingPresentationMorphism R A2 B2);
symbol p2 : τ (@CommRingPresentationMorphism R B2 D2);
symbol c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2);
symbol x2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2);
symbol am : τ (@CommRingPresentationMorphism R Am A0);
symbol bm : τ (@CommRingPresentationMorphism R Bm B0);
symbol dm : τ (@CommRingPresentationMorphism R Dm D0);
symbol fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm);
symbol a0 : τ (@CommRingPresentationMorphism R A0 A1);
symbol b0 : τ (@CommRingPresentationMorphism R B0 B1);
symbol d0 : τ (@CommRingPresentationMorphism R D0 D1);
symbol gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0);
symbol a1 : τ (@CommRingPresentationMorphism R A1 A2);
symbol b1 : τ (@CommRingPresentationMorphism R B1 B2);
symbol d1 : τ (@CommRingPresentationMorphism R D1 D2);
symbol jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1);
symbol upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0);
symbol lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1);



assert ⊢ @freyd_raw_native_window_middle_exact_evidence K R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower : τ (@FreydRawNativeWindowMiddleExactness K R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower);
assert ⊢ @freyd_raw_native_window_source_exact_evidence K R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower : τ (@FreydRawNativeWindowSourceExactness K R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower);
assert ⊢ @freyd_raw_native_window_target_exact_evidence K R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower : τ (@FreydRawNativeWindowTargetExactness K R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower);
