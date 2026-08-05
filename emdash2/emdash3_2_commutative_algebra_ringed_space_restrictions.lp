/*
  Whole ambient restrictions and supplied reflective CommRinged slices.

  The conventional slice K/U has a whole domain functor to K.  Precomposing
  the ambient structure presheaf by its opposite therefore constructs a whole
  CommRing-valued presheaf on K/U.  Object and arrow action remain owned by
  generic functor composition; a literal restriction arrow computes to its
  actual domain without adding encoded-Sigma eta or projection rules.

  A supplied reflective slice presentation retains a reflective CommRinged
  site on the actual slice together with one whole DefIso from its included
  structure presheaf to that computing ambient restriction.  This makes the
  assumption and the computational comparison explicit.  It does not claim
  that the slice topology, sheaf category, reflector, or structure-sheaf
  object was constructed from the ambient site.

  This rule-free module adds no site-morphism/continuity calculus, induced
  topology, sheaf pullback theorem, affine label, local-ring condition,
  overlap/cocycle field, scheme record, or gluing constructor.
*/

require open emdash.emdash3_2_commutative_algebra_ringed_space_covers;

/*
  Whole domain projections for the restriction-oriented total and its
  conventional opposite slice.

  Into_restr_cat(K,U) is the Sigma total over K^op, so its generic Sigma
  projection lands in K^op.  Taking the opposite produces K/U -> K.
*/
symbol into_restr_domain_func
  [K : Cat]
  (U : τ (Obj K))
  : τ (Functor (@Into_restr_cat K U) (Op_cat K))
≔ @Sigma_proj1_func (Op_cat K) (@yoneda_psh K U);

symbol slice_domain_func
  [K : Cat]
  (U : τ (Obj K))
  : τ (Functor (@Slice_cat K U) K)
≔ @Op_func
    (@Into_restr_cat K U)
    (Op_cat K)
    (@into_restr_domain_func K U);

/*
  Whole restriction of a CommRing-valued presheaf along a base functor.

  For F:A->B and O:B^op->CommRing, this is O o F^op.  The result is itself a
  whole functor; generic composition owns values, restriction maps,
  functoriality, and naturality.
*/
symbol comm_ring_psh_pullback
  [A B : Cat]
  (F : τ (Functor A B))
  (O : τ (@CommRingPsh B))
  : τ (@CommRingPsh A)
≔ @comp_cat_fapp0
    (Op_cat A)
    (Op_cat B)
    CommRing_cat
    O
    (@Op_func A B F);

// The ambient structure presheaf restricted to the actual slice K/U.
symbol reflective_comm_ringed_site_slice_ambient_psh
  [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  : τ (@CommRingPsh (@Slice_cat K U))
≔ @comm_ring_psh_pullback
    (@Slice_cat K U)
    K
    (@slice_domain_func K U)
    (@reflective_comm_ringed_site_underlying_psh K A);

// Cover-chart specialization of the same whole ambient restriction.
symbol reflective_comm_ringed_space_cover_chart_ambient_psh
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : τ (@CommRingPsh (@Slice_cat K
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)))
≔ @reflective_comm_ringed_site_slice_ambient_psh
    K
    (@reflective_comm_ringed_space_cover_ringed_site K P)
    (@reflective_comm_ringed_space_cover_chart_domain K P chart);

/*
  Assumption-explicit computational presentation of a reflective slice.

  B supplies topology, reflector, and one structure-sheaf object on K/U.
  The whole DefIso is the only relation asserted with the ambient site: the
  included presheaf of B has the computing ambient restriction as a selected
  representation.  Topology compatibility remains a separate later gate.
*/
symbol SuppliedReflectiveCommRingedSlicePresentation
  [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  : Grpd
≔ `Σ_ B : τ (@ReflectiveCommRingedSite (@Slice_cat K U)),
    @DefIso
      (@CommRingPsh_cat (@Slice_cat K U))
      (@reflective_comm_ringed_site_underlying_psh (@Slice_cat K U) B)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U);

// Constructor for the transparent supplied two-field presentation.
symbol supplied_reflective_comm_ringed_slice_intro
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  (B : τ (@ReflectiveCommRingedSite (@Slice_cat K U)))
  (comparison : τ (@DefIso
      (@CommRingPsh_cat (@Slice_cat K U))
      (@reflective_comm_ringed_site_underlying_psh (@Slice_cat K U) B)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U)))
  : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U)
≔ @Struct_sigma
    (@ReflectiveCommRingedSite (@Slice_cat K U))
    (λ B0 : τ (@ReflectiveCommRingedSite (@Slice_cat K U)),
      @DefIso
        (@CommRingPsh_cat (@Slice_cat K U))
        (@reflective_comm_ringed_site_underlying_psh (@Slice_cat K U) B0)
        (@reflective_comm_ringed_site_slice_ambient_psh K A U))
    B comparison;

// Selected supplied reflective CommRinged site on the actual slice.
symbol supplied_reflective_comm_ringed_slice_ringed_site
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  : τ (@ReflectiveCommRingedSite (@Slice_cat K U))
≔ sigma_Fst P;

// Selected topology of the supplied slice site; no induced-topology claim.
symbol supplied_reflective_comm_ringed_slice_topology
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  : τ (@GrothTopology (@Slice_cat K U))
≔ @reflective_comm_ringed_site_topology
    (@Slice_cat K U)
    (@supplied_reflective_comm_ringed_slice_ringed_site K A U P);

// Included structure presheaf of the supplied slice site.
symbol supplied_reflective_comm_ringed_slice_underlying_psh
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  : τ (@CommRingPsh (@Slice_cat K U))
≔ @reflective_comm_ringed_site_underlying_psh
    (@Slice_cat K U)
    (@supplied_reflective_comm_ringed_slice_ringed_site K A U P);

// Whole computational comparison with the restricted ambient presheaf.
symbol supplied_reflective_comm_ringed_slice_ambient_defiso
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  : τ (@DefIso
      (@CommRingPsh_cat (@Slice_cat K U))
      (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U))
≔ sigma_Snd P;

// Readable component of the whole comparison at one slice object.
symbol supplied_reflective_comm_ringed_slice_to_ambient_at
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (q : τ (Obj (@Slice_cat K U)))
  : τ (@CommRingHom
      (@comm_ring_psh_value
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
        q)
      (@comm_ring_psh_value
        (@Slice_cat K U)
        (@reflective_comm_ringed_site_slice_ambient_psh K A U)
        q))
≔ @tapp0_fapp0
    (Op_cat (@Slice_cat K U))
    CommRing_cat
    (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
    (@reflective_comm_ringed_site_slice_ambient_psh K A U)
    q
    (@defiso_to
      (@CommRingPsh_cat (@Slice_cat K U))
      (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U)
      (@supplied_reflective_comm_ringed_slice_ambient_defiso K A U P));

// Readable component of the whole inverse comparison at the same object.
symbol supplied_reflective_comm_ringed_slice_from_ambient_at
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (q : τ (Obj (@Slice_cat K U)))
  : τ (@CommRingHom
      (@comm_ring_psh_value
        (@Slice_cat K U)
        (@reflective_comm_ringed_site_slice_ambient_psh K A U)
        q)
      (@comm_ring_psh_value
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
        q))
≔ @tapp0_fapp0
    (Op_cat (@Slice_cat K U))
    CommRing_cat
    (@reflective_comm_ringed_site_slice_ambient_psh K A U)
    (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
    q
    (@defiso_from
      (@CommRingPsh_cat (@Slice_cat K U))
      (@supplied_reflective_comm_ringed_slice_underlying_psh K A U P)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U)
      (@supplied_reflective_comm_ringed_slice_ambient_defiso K A U P));
