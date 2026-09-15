/* Shared native whole P/Q row contract for concrete window consumers. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_short_exact;

// Original whole P/Q shortness at the original constant raw row.
symbol FreydAdjunctionModelRowShortExact [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) : Grpd
≔ @FreydRawNativeRowShortExact Terminal_cat R M A B D e d chain;
