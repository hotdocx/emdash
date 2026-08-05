/*
  Whole affine-basis realizations inside an ambient reflective ringed space.

  A selected affine-basis functor i:Aff_R->K/U carries supplied whole
  sheaf-category comparison semantics.  Independently, direct presheaf
  restriction keeps the ambient structure presheaf computational and one
  whole DefIso joins it to an existing AffineSchemePresentation(R).  Generic
  DefIso composition then compares it directly with affine coordinates.

  The semantic comparison and computational bridge are complementary whole
  statements; they do not add component naturality or overlap equations.
  Local exactness may later construct a sheafification/base-change mate, but
  neither such a mate nor a local-exactness derivation is retained here.

  This transparent rule-free module does not construct the basis functor,
  topology, reflector, affine presentation, or comparison evidence.  It does
  not assert equivalence of the raw base categories, transport generic glue,
  define a general scheme, or impose a stalk-local-ring condition.
*/

require open emdash.emdash3_2_site_basis;
require open emdash.emdash3_2_commutative_algebra_ringed_space_restrictions;
require open emdash.emdash3_2_commutative_algebra_affine_schemes;

// Ambient structure presheaf evaluated on the selected affine basis.
symbol ambient_affine_basis_psh
  [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (R : τ CommRing)
  (i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)))
  : τ (@CommRingPsh (@AffineSpecBigSlice_cat R))
≔ @comm_ring_psh_pullback
    (@AffineSpecBigSlice_cat R)
    (@Slice_cat K U)
    i
    (@reflective_comm_ringed_site_slice_ambient_psh K A U);

// Supplied affine-basis semantics plus one direct whole computing bridge.
symbol AffineBasisRealizationAlong
  [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (R : τ CommRing)
  (X : τ (@AffineSchemePresentation R))
  (i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)))
  : Grpd
≔ `Σ_ basis : τ (@SuppliedSheafBasisEquivalenceAlong
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)
      CommRing_cat
      (@affine_spec_big_zariski_topology R)
      (@supplied_reflective_comm_ringed_slice_topology K A U P)
      (@reflective_comm_ringed_site_sheafification
        (@AffineSpecBigSlice_cat R)
        (@affine_scheme_ringed_site R X))
      (@reflective_comm_ringed_site_sheafification
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_ringed_site K A U P))
      i),
    @DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@ambient_affine_basis_psh K A U R i)
      (@affine_scheme_underlying_psh R X);

symbol affine_basis_realization_intro
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  [P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U)]
  [R : τ CommRing]
  [X : τ (@AffineSchemePresentation R)]
  [i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U))]
  (basis : τ (@SuppliedSheafBasisEquivalenceAlong
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)
      CommRing_cat
      (@affine_spec_big_zariski_topology R)
      (@supplied_reflective_comm_ringed_slice_topology K A U P)
      (@reflective_comm_ringed_site_sheafification
        (@AffineSpecBigSlice_cat R)
        (@affine_scheme_ringed_site R X))
      (@reflective_comm_ringed_site_sheafification
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_ringed_site K A U P))
      i))
  (bridge : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@ambient_affine_basis_psh K A U R i)
      (@affine_scheme_underlying_psh R X)))
  : τ (@AffineBasisRealizationAlong K A U P R X i)
≔ @Struct_sigma
    (@SuppliedSheafBasisEquivalenceAlong
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)
      CommRing_cat
      (@affine_spec_big_zariski_topology R)
      (@supplied_reflective_comm_ringed_slice_topology K A U P)
      (@reflective_comm_ringed_site_sheafification
        (@AffineSpecBigSlice_cat R)
        (@affine_scheme_ringed_site R X))
      (@reflective_comm_ringed_site_sheafification
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_ringed_site K A U P))
      i)
    (λ _ : τ (@SuppliedSheafBasisEquivalenceAlong
        (@AffineSpecBigSlice_cat R)
        (@Slice_cat K U)
        CommRing_cat
        (@affine_spec_big_zariski_topology R)
        (@supplied_reflective_comm_ringed_slice_topology K A U P)
        (@reflective_comm_ringed_site_sheafification
          (@AffineSpecBigSlice_cat R)
          (@affine_scheme_ringed_site R X))
        (@reflective_comm_ringed_site_sheafification
          (@Slice_cat K U)
          (@supplied_reflective_comm_ringed_slice_ringed_site K A U P))
        i),
      @DefIso
        (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
        (@ambient_affine_basis_psh K A U R i)
        (@affine_scheme_underlying_psh R X))
    basis bridge;

symbol affine_basis_realization_semantics
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  [P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U)]
  [R : τ CommRing]
  [X : τ (@AffineSchemePresentation R)]
  [i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U))]
  (Q : τ (@AffineBasisRealizationAlong K A U P R X i))
  : τ (@SuppliedSheafBasisEquivalenceAlong
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)
      CommRing_cat
      (@affine_spec_big_zariski_topology R)
      (@supplied_reflective_comm_ringed_slice_topology K A U P)
      (@reflective_comm_ringed_site_sheafification
        (@AffineSpecBigSlice_cat R)
        (@affine_scheme_ringed_site R X))
      (@reflective_comm_ringed_site_sheafification
        (@Slice_cat K U)
        (@supplied_reflective_comm_ringed_slice_ringed_site K A U P))
      i)
≔ sigma_Fst Q;

symbol affine_basis_realization_bridge
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  [P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U)]
  [R : τ CommRing]
  [X : τ (@AffineSchemePresentation R)]
  [i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U))]
  (Q : τ (@AffineBasisRealizationAlong K A U P R X i))
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@ambient_affine_basis_psh K A U R i)
      (@affine_scheme_underlying_psh R X))
≔ sigma_Snd Q;

// Whole computational comparison with the existing affine coordinates.
symbol affine_basis_realization_coordinate_defiso
  [K : Cat]
  [A : τ (@ReflectiveCommRingedSite K)]
  [U : τ (Obj K)]
  [P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U)]
  [R : τ CommRing]
  [X : τ (@AffineSchemePresentation R)]
  [i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U))]
  (Q : τ (@AffineBasisRealizationAlong K A U P R X i))
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@ambient_affine_basis_psh K A U R i)
      (@affine_spec_coordinate_psh R))
≔ @defiso_comp
    (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
    (@ambient_affine_basis_psh K A U R i)
    (@affine_scheme_underlying_psh R X)
    (@affine_spec_coordinate_psh R)
    (@affine_scheme_coordinate_defiso R X)
    (@affine_basis_realization_bridge K A U P R X i Q);
