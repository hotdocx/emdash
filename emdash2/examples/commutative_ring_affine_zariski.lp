/*
  Reviewer-facing direct big-affine generated Zariski topology.
*/

require open emdash.emdash3_2_commutative_algebra_affine_zariski;

// catalog-area: Direct big-affine generated Zariski topology
// The selected localization is a whole arrow into the literal chart.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier S)]
  (localization : τ (@CommRingLocalizationAt S f)) ⊢
  @affine_spec_chart_localization_arrow R S h f localization
  : τ (Obj (@Into_restr_cat
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h)));

// Its domain is the selected localized chart with the exact internal base map.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier S)]
  (localization : τ (@CommRingLocalizationAt S f)) ⊢
  @into_restr_domain
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_chart R S h)
    (@affine_spec_chart_localization_arrow R S h f localization)
  ≡ @affine_spec_chart
      R
      (@comm_ring_localization_target S f localization)
      (@affine_spec_chart_localization_structure_map
        R S h f localization);

// Typed observation of coordinate restriction along the whole chart arrow.
symbol affine_spec_chart_localization_restriction_review
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier S)]
  (localization : τ (@CommRingLocalizationAt S f))
  : τ (@CommRingHom
      S (@comm_ring_localization_target S f localization))
≔ @comm_ring_psh_restriction_hom
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_coordinate_psh R)
    (@into_restr_domain
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h)
      (@affine_spec_chart_localization_arrow R S h f localization))
    (@affine_spec_chart R S h)
    (@into_restr_arrow
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h)
      (@affine_spec_chart_localization_arrow R S h f localization));

// Coordinate restriction computes to the supplied whole localization map.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier S)]
  (localization : τ (@CommRingLocalizationAt S f)) ⊢
  @affine_spec_chart_localization_restriction_review
    R S h f localization
  ≡ @comm_ring_localization_map S f localization;

// Formation of selected finite-family containment on one literal chart.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (family : τ (@CommRingZariskiCoverFamily S))
  (Q : τ (@Sieve
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h))) ⊢
  @AffineSpecChartZariskiCoverFamilyMembership R S h family Q
  : Grpd;

// The arbitrary-chart generator family has the expected whole-site scope.
assert (R : τ CommRing) ⊢
  @AffineSpecBigZariskiGenerators R
  : τ (@SieveGeneratorFamily (@AffineSpecBigSlice_cat R));

// The internal intersection is a complete Grothendieck topology.
assert (R : τ CommRing) ⊢
  @affine_spec_big_zariski_topology R
  : τ (@GrothTopology (@AffineSpecBigSlice_cat R));

assert (R : τ CommRing) ⊢
  @groth_topology_laws
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_big_zariski_topology R)
  : τ (@IsGrothTopology
      (@AffineSpecBigSlice_cat R)
      (@groth_topology_cover_predicate
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_big_zariski_topology R)));

// Every selected finite chart family contained in Q makes Q cover.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (family : τ (@CommRingZariskiCoverFamily S))
  (Q : τ (@Sieve
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h)))
  (members : τ (@AffineSpecChartZariskiCoverFamilyMembership
      R S h family Q)) ⊢
  @affine_spec_big_zariski_topology_covers R S h family Q members
  : τ (@groth_topology_covers
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      (@affine_spec_chart R S h)
      Q);

// Leastness maps every generated cover into any accepting topology.
assert [R : τ CommRing]
  (T : τ (@GrothTopology (@AffineSpecBigSlice_cat R)))
  (contains : τ (@GrothTopologyAcceptsGenerators
      (@AffineSpecBigSlice_cat R)
      (@AffineSpecBigZariskiGenerators R)
      T)) ⊢
  @affine_spec_big_zariski_topology_least R T contains
  : τ (@GrothTopologyLe
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      T);
