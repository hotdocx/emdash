/* Terminal-index views for the concrete native proof-CAS window.
   These partial applications retain the complete original raw telescope. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_row_context;
require open emdash.emdash3_2_commutative_algebra_freyd_native_exactness_observations;

// Existing whole middle exactness, specialized to the concrete index.
symbol FreydAdjunctionModelMiddleExactness [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) (N : τ (@FreydAdjunctionModelNormality R M))
≔ @FreydRawNativeWindowMiddleExactness Terminal_cat R M N;

symbol freyd_adjunction_model_middle_exact_evidence [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) (N : τ (@FreydAdjunctionModelNormality R M))
≔ @freyd_raw_native_window_middle_exact_evidence Terminal_cat R M N;

// Existing whole source exactness, specialized to the concrete index.
symbol FreydAdjunctionModelSourceExactness [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) (N : τ (@FreydAdjunctionModelNormality R M))
≔ @FreydRawNativeWindowSourceExactness Terminal_cat R M N;

symbol freyd_adjunction_model_source_exact_evidence [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) (N : τ (@FreydAdjunctionModelNormality R M))
≔ @freyd_raw_native_window_source_exact_evidence Terminal_cat R M N;

// Existing whole target exactness, specialized to the concrete index.
symbol FreydAdjunctionModelTargetExactness [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) (N : τ (@FreydAdjunctionModelNormality R M))
≔ @FreydRawNativeWindowTargetExactness Terminal_cat R M N;

symbol freyd_adjunction_model_target_exact_evidence [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) (N : τ (@FreydAdjunctionModelNormality R M))
≔ @freyd_raw_native_window_target_exact_evidence Terminal_cat R M N;
