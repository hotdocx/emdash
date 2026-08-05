/*
  Reviewer for Laurent coordinates on an actual inherited scheme overlap.

  The generic Laurent presentation is instantiated at the literal global
  structure rings and the two restriction homomorphisms already derived from
  the whole structure presheaf.
*/

require open emdash.emdash3_2_commutative_algebra_scheme_laurent_overlaps;

// The thin adapter has ordinary Sigma beta for its common base ring.
assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  [overlap : τ (@BinarySchemeChartOverlapPresentation K S)]
  (A : τ CommRing)
  (coordinates : τ (@CommRingLaurentOverlapPresentation
      A
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap)
      (@binary_scheme_chart_overlap_restriction0 K S overlap)
      (@binary_scheme_chart_overlap_restriction1 K S overlap))) ⊢
  @binary_scheme_laurent_overlap_base_ring
    K S overlap
    (@binary_scheme_laurent_overlap_intro K S overlap A coordinates)
  ≡ A;

// Its retained coordinate package is exactly the generic presentation on the
// actual overlap and actual structure-sheaf restrictions.
assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  [overlap : τ (@BinarySchemeChartOverlapPresentation K S)]
  (A : τ CommRing)
  (coordinates : τ (@CommRingLaurentOverlapPresentation
      A
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap)
      (@binary_scheme_chart_overlap_restriction0 K S overlap)
      (@binary_scheme_chart_overlap_restriction1 K S overlap))) ⊢
  @binary_scheme_laurent_overlap_coordinates
    K S overlap
    (@binary_scheme_laurent_overlap_intro K S overlap A coordinates)
  ≡ coordinates;
