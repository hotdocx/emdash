/*
  Reviewer for the supplied global projective-line capability.

  The package retains one already-global binary site-relative scheme, its
  actual selected chart intersection, and the existing whole Laurent overlap
  presentation.  The checks below exercise only inherited Sigma computation;
  no atlas-first gluing, disconnected transition map, componentwise cocycle,
  or external naturality field is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_projective_line;

// The three retained whole presentations compute through the constructor.
assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  (laurent : τ (@BinarySchemeLaurentOverlapPresentation K S overlap)) ⊢
  @supplied_projective_line_scheme K
    (@supplied_projective_line_intro K S overlap laurent)
  ≡ S;

assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  (laurent : τ (@BinarySchemeLaurentOverlapPresentation K S overlap)) ⊢
  @supplied_projective_line_overlap K
    (@supplied_projective_line_intro K S overlap laurent)
  ≡ overlap;

assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  (laurent : τ (@BinarySchemeLaurentOverlapPresentation K S overlap)) ⊢
  @supplied_projective_line_laurent K
    (@supplied_projective_line_intro K S overlap laurent)
  ≡ laurent;

// The common base and generic Laurent coordinates are literal projections.
assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  (A : τ CommRing)
  (coordinates : τ (@CommRingLaurentOverlapPresentation
      A
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap)
      (@binary_scheme_chart_overlap_restriction0 K S overlap)
      (@binary_scheme_chart_overlap_restriction1 K S overlap))) ⊢
  @supplied_projective_line_base_ring K
    (@supplied_projective_line_intro
      K S overlap
      (@binary_scheme_laurent_overlap_intro
        K S overlap A coordinates))
  ≡ A;

assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  (A : τ CommRing)
  (coordinates : τ (@CommRingLaurentOverlapPresentation
      A
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap)
      (@binary_scheme_chart_overlap_restriction0 K S overlap)
      (@binary_scheme_chart_overlap_restriction1 K S overlap))) ⊢
  @supplied_projective_line_coordinates K
    (@supplied_projective_line_intro
      K S overlap
      (@binary_scheme_laurent_overlap_intro
        K S overlap A coordinates))
  ≡ coordinates;

// The generic Laurent reviewer already checks that this exact retained object
// supplies both internally constructed whole transition-identity paths.
