/*
  Assumption-explicit global projective-line presentations.

  A supplied global binary site-relative scheme already owns its structure
  sheaf, local-ring capability, covering sieve, and two whole affine chart
  realizations.  A selected product in the global slice supplies the actual
  chart intersection.  Requiring the two literal structure-ring restrictions
  to carry the existing Laurent-overlap presentation then says that both
  charts are affine lines over one common base ring and that their shared
  principal opens are related by coordinate inversion.

  This dependent total is the smallest end-to-end P1 capability over the
  existing owners.  It adds no overlap or cocycle field to the general scheme
  record, no disconnected transition map, and no atlas-first gluing.  The
  global object and all semantic capabilities remain visibly supplied: this
  module does not construct Proj, prove non-affineness, or define a category
  of schemes.
*/

require open emdash.emdash3_2_commutative_algebra_scheme_laurent_overlaps;

// One supplied global scheme, its actual chart intersection, and Laurent data.
symbol SuppliedProjectiveLinePresentation
  (K : Cat)
  : Grpd
≔ `Σ_ S : τ (@BinarySiteRelativeSchemePresentation K),
   `Σ_ overlap : τ (@BinarySchemeChartOverlapPresentation K S),
      @BinarySchemeLaurentOverlapPresentation K S overlap;

// Constructor retaining each existing whole presentation exactly once.
symbol supplied_projective_line_intro
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  (coordinates : τ (@BinarySchemeLaurentOverlapPresentation
      K S overlap))
  : τ (@SuppliedProjectiveLinePresentation K)
≔ @Struct_sigma
    (@BinarySiteRelativeSchemePresentation K)
    (λ S0 : τ (@BinarySiteRelativeSchemePresentation K),
      `Σ_ overlap0 : τ (@BinarySchemeChartOverlapPresentation K S0),
        @BinarySchemeLaurentOverlapPresentation K S0 overlap0)
    S
    (@Struct_sigma
      (@BinarySchemeChartOverlapPresentation K S)
      (λ overlap0 : τ (@BinarySchemeChartOverlapPresentation K S),
        @BinarySchemeLaurentOverlapPresentation K S overlap0)
      overlap coordinates);

// Retained global binary site-relative scheme.
symbol supplied_projective_line_scheme
  [K : Cat]
  (P : τ (@SuppliedProjectiveLinePresentation K))
  : τ (@BinarySiteRelativeSchemePresentation K)
≔ sigma_Fst P;

// Selected actual intersection of the two retained global charts.
symbol supplied_projective_line_overlap
  [K : Cat]
  (P : τ (@SuppliedProjectiveLinePresentation K))
  : τ (@BinarySchemeChartOverlapPresentation K (sigma_Fst P))
≔ sigma_Fst (sigma_Snd P);

// Laurent-coordinate presentation on that literal inherited intersection.
symbol supplied_projective_line_laurent
  [K : Cat]
  (P : τ (@SuppliedProjectiveLinePresentation K))
  : τ (@BinarySchemeLaurentOverlapPresentation
      K (sigma_Fst P) (sigma_Fst (sigma_Snd P)))
≔ sigma_Snd (sigma_Snd P);

// Common base ring over which both actual chart rings are polynomial lines.
symbol supplied_projective_line_base_ring
  [K : Cat]
  (P : τ (@SuppliedProjectiveLinePresentation K))
  : τ CommRing
≔ sigma_Fst (sigma_Snd (sigma_Snd P));

// Generic Laurent package specialized to the actual rings and restrictions.
symbol supplied_projective_line_coordinates
  [K : Cat]
  (P : τ (@SuppliedProjectiveLinePresentation K))
  : τ (@CommRingLaurentOverlapPresentation
      (sigma_Fst (sigma_Snd (sigma_Snd P)))
      (@binary_scheme_chart0_structure_ring K (sigma_Fst P))
      (@binary_scheme_chart1_structure_ring K (sigma_Fst P))
      (@binary_scheme_chart_overlap_ring
        K (sigma_Fst P) (sigma_Fst (sigma_Snd P)))
      (@binary_scheme_chart_overlap_restriction0
        K (sigma_Fst P) (sigma_Fst (sigma_Snd P)))
      (@binary_scheme_chart_overlap_restriction1
        K (sigma_Fst P) (sigma_Fst (sigma_Snd P))))
≔ sigma_Snd (sigma_Snd (sigma_Snd P));
