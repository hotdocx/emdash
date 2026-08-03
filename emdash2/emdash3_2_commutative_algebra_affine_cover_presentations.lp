/*
  Global-first computational binary affine-cover presentations.

  The retained global reflective ringed-space cover supplies the actual
  object, structure presheaf, covering sieve, and internally stable pullbacks.
  Two selected cover members carry constructive generation: every arrow in
  the covering sieve factors through one Boolean-selected chart.  Each chart
  then carries one whole AffineCoverChartRealization relating its actual
  ambient restriction to computing affine coordinates.

  Overlaps and repeated restrictions remain derived from the global object
  and generic composition.  This transparent, rule-free package stores no
  external naturality, overlap, or cocycle family.  It is an affine-cover
  presentation, not yet a locally-ringed SchemePresentation or an atlas-first
  gluing constructor.
*/

require open emdash.emdash3_2_commutative_algebra_binary_covers;
require open emdash.emdash3_2_commutative_algebra_affine_cover_charts;

// Two charts generating the retained cover, with whole affine realizations.
symbol BinaryAffineCoverPresentation
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : Grpd
≔ `Σ_ chart0 : τ (@ReflectiveCommRingedSpaceCoverChart K P),
   `Σ_ chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P),
   `Σ_ generation : τ (@BinarySelectedCoverGeneration
        K P chart0 chart1),
   `Σ_ affine0 : τ (@AffineCoverChartRealization K P chart0),
      @AffineCoverChartRealization K P chart1;

symbol binary_affine_cover_intro
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (generation : τ (@BinarySelectedCoverGeneration K P chart0 chart1))
  (affine0 : τ (@AffineCoverChartRealization K P chart0))
  (affine1 : τ (@AffineCoverChartRealization K P chart1))
  : τ (@BinaryAffineCoverPresentation K P)
≔ @Struct_sigma
    (@ReflectiveCommRingedSpaceCoverChart K P)
    (λ chart00 : τ (@ReflectiveCommRingedSpaceCoverChart K P),
      `Σ_ chart10 : τ (@ReflectiveCommRingedSpaceCoverChart K P),
      `Σ_ generation0 : τ (@BinarySelectedCoverGeneration
          K P chart00 chart10),
      `Σ_ affine00 : τ (@AffineCoverChartRealization K P chart00),
        @AffineCoverChartRealization K P chart10)
    chart0
    (@Struct_sigma
      (@ReflectiveCommRingedSpaceCoverChart K P)
      (λ chart10 : τ (@ReflectiveCommRingedSpaceCoverChart K P),
        `Σ_ generation0 : τ (@BinarySelectedCoverGeneration
            K P chart0 chart10),
        `Σ_ affine00 : τ (@AffineCoverChartRealization K P chart0),
          @AffineCoverChartRealization K P chart10)
      chart1
      (@Struct_sigma
        (@BinarySelectedCoverGeneration K P chart0 chart1)
        (λ _ : τ (@BinarySelectedCoverGeneration K P chart0 chart1),
          `Σ_ affine00 : τ (@AffineCoverChartRealization K P chart0),
            @AffineCoverChartRealization K P chart1)
        generation
        (@Struct_sigma
          (@AffineCoverChartRealization K P chart0)
          (λ _ : τ (@AffineCoverChartRealization K P chart0),
            @AffineCoverChartRealization K P chart1)
          affine0 affine1)));

// Readable first selected chart.
symbol binary_affine_cover_chart0
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  : τ (@ReflectiveCommRingedSpaceCoverChart K P)
≔ sigma_Fst Q;

// Readable second selected chart.
symbol binary_affine_cover_chart1
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  : τ (@ReflectiveCommRingedSpaceCoverChart K P)
≔ sigma_Fst (sigma_Snd Q);

// Retained constructive generation at the literal chart projections.
symbol binary_affine_cover_generation
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  : τ (@BinarySelectedCoverGeneration
      K P
      (sigma_Fst Q)
      (sigma_Fst (sigma_Snd Q)))
≔ sigma_Fst (sigma_Snd (sigma_Snd Q));

// Whole affine realization of the first chart.
symbol binary_affine_cover_realization0
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  : τ (@AffineCoverChartRealization K P (sigma_Fst Q))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd Q)));

// Whole affine realization of the second chart.
symbol binary_affine_cover_realization1
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (Q : τ (@BinaryAffineCoverPresentation K P))
  : τ (@AffineCoverChartRealization
      K P (sigma_Fst (sigma_Snd Q)))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd Q)));
