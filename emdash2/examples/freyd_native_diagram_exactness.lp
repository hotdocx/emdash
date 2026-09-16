require open emdash.emdash3_2_commutative_algebra_freyd_native_diagram_exactness;

// The actual coherent diagram and its fixed input family index the result.
assert [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M)) [n : τ Nat_grpd]
 (inputs : τ (@FiniteFamily (FreydNativeInput R) n)) (first : τ (FreydArrowObservation R)) (arrows : τ
  (@FiniteFamily (FreydArrowObservation R) n))
 (matching : τ (@FreydArrowMatchingTail R first n arrows))
 (E : τ (@FreydNativeObservedExactTail R M N n inputs first arrows)) ⊢ (@freyd_native_exact_diagram_intro R
  M N n inputs first arrows matching E) : τ (@FreydNativeDiagramExactness R M N n inputs
 (@freyd_arrow_diagram_intro R n first arrows matching));

// Assembly retains the original indexed certificate data.
assert [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M)) [n : τ Nat_grpd]
 (inputs : τ (@FiniteFamily (FreydNativeInput R) n)) (first : τ (FreydArrowObservation R)) (arrows : τ
  (@FiniteFamily (FreydArrowObservation R) n))
 (matching : τ (@FreydArrowMatchingTail R first n arrows))
 (E : τ (@FreydNativeObservedExactTail R M N n inputs first arrows)) ⊢ (@freyd_native_exact_diagram_intro R
  M N n inputs first arrows matching E) ≡ E;
