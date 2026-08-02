/*
  Direct big-affine generated Zariski topology.

  A selected localization of a literal chart R -> S becomes a whole arrow in
  Aff/Spec(R). Its target structure map is the exact existing opposite-
  precomposition endpoint, making the chart triangle reflexive. One outer
  sigma_ind exposes an arbitrary slice object's retained chart before finite
  localization-family containment is used as witness-rich generator data.

  The generic internal intersection then constructs the least topology. This
  transparent, rule-free module adds no Sigma eta, external naturality or
  triangle field, coverhood rewrite, localization choice, sheaf, or scheme.
*/

require open emdash.emdash3_2_generated_topologies;
require open emdash.emdash3_2_commutative_algebra_affine_spec;

// Exact internal composite R -> S -> S[1/f] used by the Sigma-arrow owner.
symbol affine_spec_chart_localization_structure_map
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier S)]
  (localization : τ (@CommRingLocalizationAt S f))
  : τ (@CommRingHom
      R (@comm_ring_localization_target S f localization))
≔ @hom_precomp_along_fapp0
    (Op_cat CommRing_cat)
    (Op_cat CommRing_cat)
    (@id_func (Op_cat CommRing_cat))
    R
    (@comm_ring_localization_target S f localization)
    S
    (@comm_ring_localization_map S f localization)
    h;

// A selected localization as a whole arrow into the literal affine chart.
symbol affine_spec_chart_localization_arrow
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  [f : τ (@comm_ring_carrier S)]
  (localization : τ (@CommRingLocalizationAt S f))
  : τ (Obj (@Into_restr_cat
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h)))
≔ @Struct_sigma
    (Obj (@AffineSpecBigSlice_cat R))
    (λ V : τ (Obj (@AffineSpecBigSlice_cat R)),
      Hom
        (@AffineSpecBigSlice_cat R)
        V
        (@affine_spec_chart R S h))
    (@affine_spec_chart
      R
      (@comm_ring_localization_target S f localization)
      (@affine_spec_chart_localization_structure_map
        R S h f localization))
    (@affine_spec_chart_arrow
      R S
      (@comm_ring_localization_target S f localization)
      h
      (@affine_spec_chart_localization_structure_map
        R S h f localization)
      (@comm_ring_localization_map S f localization)
      (@eq_refl
        (@CommRingHom
          R (@comm_ring_localization_target S f localization))
        (@affine_spec_chart_localization_structure_map
          R S h f localization)));

// Explicit containment of every lifted chart in one selected finite family.
symbol AffineSpecChartZariskiCoverFamilyMembership
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (family : τ (@CommRingZariskiCoverFamily S))
  (Q : τ (@Sieve
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h)))
  : Grpd
≔ @FiniteFamilyAllOver
    (@comm_ring_carrier S)
    (λ f : τ (@comm_ring_carrier S), @CommRingLocalizationAt S f)
    (λ f : τ (@comm_ring_carrier S),
      λ localization : τ (@CommRingLocalizationAt S f),
        @SieveMembership
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_chart R S h)
          Q
          (@affine_spec_chart_localization_arrow
            R S h f localization))
    (@comm_ring_zariski_cover_family_length S family)
    (@comm_ring_zariski_cover_family_generators S family)
    (@comm_ring_zariski_cover_family_localizations S family);

// Witness-rich selected finite Zariski generators on the relative big site.
symbol AffineSpecBigZariskiGenerators
  (R : τ CommRing)
  : τ (@SieveGeneratorFamily (@AffineSpecBigSlice_cat R))
≔ λ U : τ (Obj (@AffineSpecBigSlice_cat R)),
   @sigma_ind
     (Obj CommRing_cat)
     (λ S : τ (Obj CommRing_cat),
       Obj (@Fibre_cat
         CommRing_cat
         (@yoneda_psh (Op_cat CommRing_cat) R)
         S))
     (λ U0 : @τΣ_
         (Obj CommRing_cat)
         (λ S : τ (Obj CommRing_cat),
           Obj (@Fibre_cat
             CommRing_cat
             (@yoneda_psh (Op_cat CommRing_cat) R)
             S)),
       @Pi_grpd
         (@Sieve (@AffineSpecBigSlice_cat R) U0)
         (λ _ : τ (@Sieve (@AffineSpecBigSlice_cat R) U0),
           Obj Grpd_cat))
     (λ S : τ (Obj CommRing_cat),
       λ h : τ (Obj (@Fibre_cat
         CommRing_cat
         (@yoneda_psh (Op_cat CommRing_cat) R)
         S)),
       λ Q : τ (@Sieve
         (@AffineSpecBigSlice_cat R)
         (@affine_spec_chart R S h)),
         `Σ_ family : τ (@CommRingZariskiCoverFamily S),
           @AffineSpecChartZariskiCoverFamilyMembership R S h family Q)
     U;

// The internally constructed least big Zariski topology over Spec(R).
symbol affine_spec_big_zariski_topology
  (R : τ CommRing)
  : τ (@GrothTopology (@AffineSpecBigSlice_cat R))
≔ @generated_groth_topology
    (@AffineSpecBigSlice_cat R)
    (@AffineSpecBigZariskiGenerators R);

// Every selected affine Zariski presentation covers in the generated site.
symbol affine_spec_big_zariski_topology_covers
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (family : τ (@CommRingZariskiCoverFamily S))
  (Q : τ (@Sieve
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_chart R S h)))
  (members : τ (@AffineSpecChartZariskiCoverFamilyMembership
      R S h family Q))
  : τ (@groth_topology_covers
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      (@affine_spec_chart R S h)
      Q)
≔ @generated_groth_topology_accepts_generators
    (@AffineSpecBigSlice_cat R)
    (@AffineSpecBigZariskiGenerators R)
    (@affine_spec_chart R S h)
    Q
    (@Struct_sigma
      (@CommRingZariskiCoverFamily S)
      (λ family0 : τ (@CommRingZariskiCoverFamily S),
        @AffineSpecChartZariskiCoverFamilyMembership R S h family0 Q)
      family members);

// Universal property of the selected relative big Zariski topology.
symbol affine_spec_big_zariski_topology_least
  [R : τ CommRing]
  (T : τ (@GrothTopology (@AffineSpecBigSlice_cat R)))
  (contains : τ (@GrothTopologyAcceptsGenerators
      (@AffineSpecBigSlice_cat R)
      (@AffineSpecBigZariskiGenerators R)
      T))
  : τ (@GrothTopologyLe
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      T)
≔ @generated_groth_topology_least
    (@AffineSpecBigSlice_cat R)
    (@AffineSpecBigZariskiGenerators R)
    T contains;
