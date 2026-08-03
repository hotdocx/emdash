/*
  Total binary site-relative computational scheme presentations.

  The global reflective CommRinged object already owns its whole structure
  sheaf, restriction, and compatibility. Its dependent certificate supplies
  topology-local local-ring computation and two constructively generating
  affine charts with whole ambient-to-affine realizations. Totaling those
  existing layers gives one end-user presentation without storing overlap,
  transition, cocycle, or gluing data again.

  The site-relative qualifier is essential: the supplied topology determines
  admissible chart geometry. This transparent, rule-free module does not
  claim a representation-independent Scheme category, classical Zariski-open
  comparison, Zeuner compact-open classifier, atlas-first construction,
  effectivity theorem, or projective-space construction.
*/

require open emdash.emdash3_2_commutative_algebra_locally_ringed_space_presentations;

// One global object with its complete binary site-relative presentation.
symbol BinarySiteRelativeSchemePresentation
  (K : Cat)
  : Grpd
≔ `Σ_ P : τ (@ReflectiveCommRingedSpaceCover K),
      @BinaryLocallyRingedAffineCoverPresentation K P;

// Constructor retaining the global object and its certificate exactly once.
symbol binary_site_relative_scheme_intro
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P))
  : τ (@BinarySiteRelativeSchemePresentation K)
≔ @Struct_sigma
    (@ReflectiveCommRingedSpaceCover K)
    (λ P0 : τ (@ReflectiveCommRingedSpaceCover K),
      @BinaryLocallyRingedAffineCoverPresentation K P0)
    P Q;

// Retained global reflective ringed object and covering sieve.
symbol binary_site_relative_scheme_global_cover
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@ReflectiveCommRingedSpaceCover K)
≔ sigma_Fst S;

// Dependent locally-ringed affine-atlas certificate at the canonical endpoint.
symbol binary_site_relative_scheme_certificate
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@BinaryLocallyRingedAffineCoverPresentation K (sigma_Fst S))
≔ sigma_Snd S;

// Global reflective CommRinged site.
symbol binary_site_relative_scheme_ringed_site
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@ReflectiveCommRingedSite K)
≔ @reflective_comm_ringed_space_cover_ringed_site
    K (sigma_Fst S);

// Distinguished global object whose restrictions are presented.
symbol binary_site_relative_scheme_whole_object
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (Obj K)
≔ @reflective_comm_ringed_space_cover_whole_object
    K (sigma_Fst S);

// Whole global CommRing-valued structure presheaf.
symbol binary_site_relative_scheme_underlying_psh
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@CommRingPsh K)
≔ @reflective_comm_ringed_space_cover_underlying_psh
    K (sigma_Fst S);

// Selected covering sieve on the global object.
symbol binary_site_relative_scheme_cover_sieve
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@Sieve K
      (@reflective_comm_ringed_space_cover_whole_object K (sigma_Fst S)))
≔ @reflective_comm_ringed_space_cover_sieve
    K (sigma_Fst S);

// Retained topology-local whole-object capability.
symbol binary_site_relative_scheme_local
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@ReflectiveCommRingedWholeObjectLocalPresentation
      K (sigma_Fst S))
≔ @binary_locally_ringed_affine_cover_local
    K (sigma_Fst S) (sigma_Snd S);

// Retained constructively generated binary affine atlas.
symbol binary_site_relative_scheme_atlas
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@BinaryAffineCoverPresentation K (sigma_Fst S))
≔ @binary_locally_ringed_affine_cover_atlas
    K (sigma_Fst S) (sigma_Snd S);

// First selected affine generator.
symbol binary_site_relative_scheme_chart0
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@ReflectiveCommRingedSpaceCoverChart K (sigma_Fst S))
≔ @binary_affine_cover_chart0
    K (sigma_Fst S)
    (@binary_site_relative_scheme_atlas K S);

// Second selected affine generator.
symbol binary_site_relative_scheme_chart1
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@ReflectiveCommRingedSpaceCoverChart K (sigma_Fst S))
≔ @binary_affine_cover_chart1
    K (sigma_Fst S)
    (@binary_site_relative_scheme_atlas K S);

// Whole affine realization of the first selected generator.
symbol binary_site_relative_scheme_realization0
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@AffineCoverChartRealization
      K (sigma_Fst S)
      (sigma_Fst (sigma_Snd (sigma_Snd S))))
≔ @binary_affine_cover_realization0
    K (sigma_Fst S)
    (sigma_Snd (sigma_Snd S));

// Whole affine realization of the second selected generator.
symbol binary_site_relative_scheme_realization1
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ (@AffineCoverChartRealization
      K (sigma_Fst S)
      (sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd S)))))
≔ @binary_affine_cover_realization1
    K (sigma_Fst S)
    (sigma_Snd (sigma_Snd S));
