/*
  Reviewer for total binary site-relative scheme presentations.

  The constructor packages one already-global reflective ringed object and
  its dependent local/affine certificate. The whole structure presheaf,
  topology-local capability, binary atlas, selected charts, and affine
  realizations remain existing owners. No overlap, cocycle, transition, or
  atlas-first gluing input is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_site_relative_schemes;

// Both primitive fields compute through the dependent Sigma constructor.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_global_cover
    K (@binary_site_relative_scheme_intro K P Q)
  ≡ P;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_certificate
    K (@binary_site_relative_scheme_intro K P Q)
  ≡ Q;

// The global whole structure presheaf is inherited without a second field.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_underlying_psh
    K (@binary_site_relative_scheme_intro K P Q)
  ≡ @reflective_comm_ringed_space_cover_underlying_psh K P;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_ringed_site
    K (@binary_site_relative_scheme_intro K P Q)
  ≡ @reflective_comm_ringed_space_cover_ringed_site K P;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_whole_object
    K (@binary_site_relative_scheme_intro K P Q)
  ≡ @reflective_comm_ringed_space_cover_whole_object K P;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (Q : τ (@BinaryLocallyRingedAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_cover_sieve
    K (@binary_site_relative_scheme_intro K P Q)
  ≡ @reflective_comm_ringed_space_cover_sieve K P;

// Both halves of the existing certificate remain literal projections.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (local : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  (atlas : τ (@BinaryAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_local
    K
    (@binary_site_relative_scheme_intro
      K P
      (@binary_locally_ringed_affine_cover_intro K P local atlas))
  ≡ local;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (local : τ (@ReflectiveCommRingedWholeObjectLocalPresentation K P))
  (atlas : τ (@BinaryAffineCoverPresentation K P)) ⊢
  @binary_site_relative_scheme_atlas
    K
    (@binary_site_relative_scheme_intro
      K P
      (@binary_locally_ringed_affine_cover_intro K P local atlas))
  ≡ atlas;

// Selected chart observations and whole realizations retain exact types.
assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K)) ⊢
  @binary_site_relative_scheme_chart0 K S
  : τ (@ReflectiveCommRingedSpaceCoverChart
      K (@binary_site_relative_scheme_global_cover K S));

assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K)) ⊢
  @binary_site_relative_scheme_chart1 K S
  : τ (@ReflectiveCommRingedSpaceCoverChart
      K (@binary_site_relative_scheme_global_cover K S));

assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K)) ⊢
  @binary_site_relative_scheme_realization0 K S
  : τ (@AffineCoverChartRealization
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart0 K S));

assert [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K)) ⊢
  @binary_site_relative_scheme_realization1 K S
  : τ (@AffineCoverChartRealization
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart1 K S));
