/*
  Reviewer for global-first binary affine-cover presentations.

  The binary package combines two selected charts, constructive generation
  over the actual global covering sieve, and two already-whole affine chart
  realizations.  Constructor fields compute through canonical Sigma owners.
  No package eta, external overlap/cocycle family, local-ring condition, or
  scheme/gluing claim is used.
*/

require open emdash.emdash3_2_commutative_algebra_affine_cover_presentations;

// The binary constructor exposes both charts and its generation witness.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (generation : τ (@BinarySelectedCoverGeneration K P chart0 chart1))
  (affine0 : τ (@AffineCoverChartRealization K P chart0))
  (affine1 : τ (@AffineCoverChartRealization K P chart1)) ⊢
  @binary_affine_cover_chart1
    K P
    (@binary_affine_cover_intro
      K P chart0 chart1 generation affine0 affine1)
  ≡ chart1;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (generation : τ (@BinarySelectedCoverGeneration K P chart0 chart1))
  (affine0 : τ (@AffineCoverChartRealization K P chart0))
  (affine1 : τ (@AffineCoverChartRealization K P chart1)) ⊢
  @binary_affine_cover_generation
    K P
    (@binary_affine_cover_intro
      K P chart0 chart1 generation affine0 affine1)
  ≡ generation;

// Both whole affine realizations remain exact retained fields.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (generation : τ (@BinarySelectedCoverGeneration K P chart0 chart1))
  (affine0 : τ (@AffineCoverChartRealization K P chart0))
  (affine1 : τ (@AffineCoverChartRealization K P chart1)) ⊢
  @binary_affine_cover_realization0
    K P
    (@binary_affine_cover_intro
      K P chart0 chart1 generation affine0 affine1)
  ≡ affine0;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (generation : τ (@BinarySelectedCoverGeneration K P chart0 chart1))
  (affine0 : τ (@AffineCoverChartRealization K P chart0))
  (affine1 : τ (@AffineCoverChartRealization K P chart1)) ⊢
  @binary_affine_cover_realization1
    K P
    (@binary_affine_cover_intro
      K P chart0 chart1 generation affine0 affine1)
  ≡ affine1;
