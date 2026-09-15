/* Native whole contracts over the original retained model adapter. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_adapter;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_short_exact;

// Alias of native whole Coim⇒Im normality at the original whole P/Q.
symbol FreydHomologyModelNativeNormality [R : τ CommRing] (M : τ (FreydHomologyModel R)) : Grpd
≔ @FreydAdjunctionModelNormality R (@freyd_homology_model_adjunctions R M);

// Alias of whole P/Q shortness at the original constant raw row.
symbol FreydHomologyModelNativeShortExact [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) : Grpd
≔ @FreydRawNativeRowShortExact Terminal_cat R (@freyd_homology_model_adjunctions R M) A B D e d chain;
