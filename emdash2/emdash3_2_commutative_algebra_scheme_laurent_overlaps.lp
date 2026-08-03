/*
  Laurent coordinates on the actual inherited overlap of a supplied scheme.

  The scheme and its selected binary product already own the global structure
  presheaf, both chart objects, their common restriction, and both restriction
  homomorphisms.  This thin dependent adapter adds one common base ring and
  applies the generic Laurent-overlap presentation directly to those literal
  rings and maps.  Consequently neither a disconnected overlap isomorphism
  nor an external restriction square is stored.

  The module is transparent and rule-free. It does not add transition or
  cocycle fields to the general scheme record, construct the global object by
  gluing, prove non-affineness, or claim a closed projective-line object.
*/

require open emdash.emdash3_2_commutative_algebra_laurent;
require open emdash.emdash3_2_commutative_algebra_scheme_chart_overlaps;

symbol BinarySchemeLaurentOverlapPresentation
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : Grpd
≔ `Σ_ A : τ CommRing,
    @CommRingLaurentOverlapPresentation
      A
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap)
      (@binary_scheme_chart_overlap_restriction0 K S overlap)
      (@binary_scheme_chart_overlap_restriction1 K S overlap);

symbol binary_scheme_laurent_overlap_intro
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  [overlap : τ (@BinarySchemeChartOverlapPresentation K S)]
  (A : τ CommRing)
  (coordinates : τ (@CommRingLaurentOverlapPresentation
      A
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap)
      (@binary_scheme_chart_overlap_restriction0 K S overlap)
      (@binary_scheme_chart_overlap_restriction1 K S overlap)))
  : τ (@BinarySchemeLaurentOverlapPresentation K S overlap)
≔ @Struct_sigma
    CommRing
    (λ A0 : τ CommRing,
      @CommRingLaurentOverlapPresentation
        A0
        (@binary_scheme_chart0_structure_ring K S)
        (@binary_scheme_chart1_structure_ring K S)
        (@binary_scheme_chart_overlap_ring K S overlap)
        (@binary_scheme_chart_overlap_restriction0 K S overlap)
        (@binary_scheme_chart_overlap_restriction1 K S overlap))
    A coordinates;

symbol binary_scheme_laurent_overlap_base_ring
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  [overlap : τ (@BinarySchemeChartOverlapPresentation K S)]
  (P : τ (@BinarySchemeLaurentOverlapPresentation K S overlap))
  : τ CommRing
≔ sigma_Fst P;

symbol binary_scheme_laurent_overlap_coordinates
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  [overlap : τ (@BinarySchemeChartOverlapPresentation K S)]
  (P : τ (@BinarySchemeLaurentOverlapPresentation K S overlap))
  : τ (@CommRingLaurentOverlapPresentation
      (sigma_Fst P)
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap)
      (@binary_scheme_chart_overlap_restriction0 K S overlap)
      (@binary_scheme_chart_overlap_restriction1 K S overlap))
≔ sigma_Snd P;
