/*
  Global reflective CommRinged objects with a selected covering sieve.

  The package retains one reflective CommRinged site, one distinguished
  global object of its base category, and one sieve covering that object in
  the site's selected topology. Pulling the cover back along any arrow is
  covering by the existing Grothendieck-stability owner. A selected cover
  member exposes its actual restriction arrow, and its pulled-back cover is
  the global-first overlap neighbourhood for later chart consumers.

  This transparent module adds no rules. It does not assert that the selected
  cover is finite or affine, impose a locally-ringed support condition, define
  a scheme, store overlap/cocycle witnesses, or construct gluing.
*/

require open emdash.emdash3_2_ringed_sites;

// A reflective CommRinged global object with one selected covering sieve.
symbol ReflectiveCommRingedSpaceCover (K : Cat) : Grpd
≔ `Σ_ A : τ (@ReflectiveCommRingedSite K),
   `Σ_ X : τ (Obj K),
   `Σ_ R : τ (@Sieve K X),
      @groth_topology_covers
        K (@reflective_comm_ringed_site_topology K A) X R;

// Constructor for the transparent four-field presentation.
symbol reflective_comm_ringed_space_cover_intro
  [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (X : τ (Obj K))
  (R : τ (@Sieve K X))
  (covers : τ (@groth_topology_covers
      K (@reflective_comm_ringed_site_topology K A) X R))
  : τ (@ReflectiveCommRingedSpaceCover K)
≔ @Struct_sigma
    (@ReflectiveCommRingedSite K)
    (λ A0 : τ (@ReflectiveCommRingedSite K),
      `Σ_ X0 : τ (Obj K),
      `Σ_ R0 : τ (@Sieve K X0),
        @groth_topology_covers
          K (@reflective_comm_ringed_site_topology K A0) X0 R0)
    A
    (@Struct_sigma
      (Obj K)
      (λ X0 : τ (Obj K),
        `Σ_ R0 : τ (@Sieve K X0),
          @groth_topology_covers
            K (@reflective_comm_ringed_site_topology K A) X0 R0)
      X
      (@Struct_sigma
        (@Sieve K X)
        (λ R0 : τ (@Sieve K X),
          @groth_topology_covers
            K (@reflective_comm_ringed_site_topology K A) X R0)
        R covers));

// Selected reflective CommRinged site.
symbol reflective_comm_ringed_space_cover_ringed_site
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : τ (@ReflectiveCommRingedSite K)
≔ sigma_Fst P;

// Topology routed through the selected ringed-site owner.
symbol reflective_comm_ringed_space_cover_topology
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : τ (@GrothTopology K)
≔ @reflective_comm_ringed_site_topology
    K (@reflective_comm_ringed_space_cover_ringed_site K P);

// Distinguished global object of the site base.
symbol reflective_comm_ringed_space_cover_whole_object
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : τ (Obj K)
≔ sigma_Fst (sigma_Snd P);

// Selected ordinary covering sieve on the distinguished object.
symbol reflective_comm_ringed_space_cover_sieve
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : τ (@Sieve K (@reflective_comm_ringed_space_cover_whole_object K P))
≔ sigma_Fst (sigma_Snd (sigma_Snd P));

// Retained evidence that the selected sieve covers.
symbol reflective_comm_ringed_space_cover_covers
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : τ (@groth_topology_covers
      K
      (@reflective_comm_ringed_space_cover_topology K P)
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P))
≔ sigma_Snd (sigma_Snd (sigma_Snd P));

// Whole included CommRing-valued structure presheaf of the retained site.
symbol reflective_comm_ringed_space_cover_underlying_psh
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : τ (@CommRingPsh K)
≔ @reflective_comm_ringed_site_underlying_psh
    K (@reflective_comm_ringed_space_cover_ringed_site K P);

// Restrict the selected cover along any arrow into the global object.
symbol reflective_comm_ringed_space_cover_pullback_sieve
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  [V : τ (Obj K)]
  (f : τ (Hom K V
      (@reflective_comm_ringed_space_cover_whole_object K P)))
  : τ (@Sieve K V)
≔ @sieve_pullback
    K V
    (@reflective_comm_ringed_space_cover_whole_object K P)
    f
    (@reflective_comm_ringed_space_cover_sieve K P);

// Grothendieck stability makes every such restricted sieve covering.
symbol reflective_comm_ringed_space_cover_pullback_covers
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  [V : τ (Obj K)]
  (f : τ (Hom K V
      (@reflective_comm_ringed_space_cover_whole_object K P)))
  : τ (@groth_topology_covers
      K
      (@reflective_comm_ringed_space_cover_topology K P)
      V
      (@reflective_comm_ringed_space_cover_pullback_sieve K P V f))
≔ (@groth_topology_pullback
      K (@reflective_comm_ringed_space_cover_topology K P))
    (@reflective_comm_ringed_space_cover_whole_object K P)
    V f
    (@reflective_comm_ringed_space_cover_sieve K P)
    (@reflective_comm_ringed_space_cover_covers K P);

/*
  A selected chart is only a member of the retained covering sieve. The name
  does not assert affineness: that later capability must compare the ambient
  restriction honestly with an affine presentation.
*/
symbol ReflectiveCommRingedSpaceCoverChart
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  : Grpd
≔ `Σ_ f : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))),
    @SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      f;

// Constructor for an actual member of the selected covering sieve.
symbol reflective_comm_ringed_space_cover_chart_intro
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (f : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (member : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      f))
  : τ (@ReflectiveCommRingedSpaceCoverChart K P)
≔ @Struct_sigma
    (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))
    (λ f0 : τ (Obj (@Into_restr_cat K
        (@reflective_comm_ringed_space_cover_whole_object K P))),
      @SieveMembership
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        (@reflective_comm_ringed_space_cover_sieve K P)
        f0)
    f member;

// Restriction-total presentation `(V,f)` of the selected member.
symbol reflective_comm_ringed_space_cover_chart_restriction
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))
≔ sigma_Fst chart;

// Domain object V of the selected restriction arrow.
symbol reflective_comm_ringed_space_cover_chart_domain
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : τ (Obj K)
≔ @into_restr_domain
    K
    (@reflective_comm_ringed_space_cover_whole_object K P)
    (@reflective_comm_ringed_space_cover_chart_restriction K P chart);

// Actual chart arrow V -> X.
symbol reflective_comm_ringed_space_cover_chart_arrow
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : τ (Hom K
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      (@reflective_comm_ringed_space_cover_whole_object K P))
≔ @into_restr_arrow
    K
    (@reflective_comm_ringed_space_cover_whole_object K P)
    (@reflective_comm_ringed_space_cover_chart_restriction K P chart);

// Retained membership evidence for the selected arrow.
symbol reflective_comm_ringed_space_cover_chart_member
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      (@reflective_comm_ringed_space_cover_chart_restriction K P chart))
≔ sigma_Snd chart;

// The global cover restricted to a selected chart is again covering.
symbol reflective_comm_ringed_space_cover_chart_pullback_covers
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : τ (@groth_topology_covers
      K
      (@reflective_comm_ringed_space_cover_topology K P)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      (@reflective_comm_ringed_space_cover_pullback_sieve
        K P
        (@reflective_comm_ringed_space_cover_chart_domain K P chart)
        (@reflective_comm_ringed_space_cover_chart_arrow K P chart)))
≔ @reflective_comm_ringed_space_cover_pullback_covers
    K P
    (@reflective_comm_ringed_space_cover_chart_domain K P chart)
    (@reflective_comm_ringed_space_cover_chart_arrow K P chart);
