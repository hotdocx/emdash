/*
  Reviewer for whole computational affine-basis realization.

  The actual ambient slice presheaf remains computational after restriction
  to a selected affine basis.  A realization retains whole sheaf-basis
  semantics and one whole DefIso to an existing affine scheme; composing that
  bridge gives the whole comparison with computing coordinates.

  No raw category equivalence, induced topology, constructed reflector,
  component naturality, local-exact square, or glue base-change is claimed.
*/

require open emdash.emdash3_2_commutative_algebra_affine_basis;

// Direct whole restriction keeps the computing value normal form.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (R : τ CommRing)
  (i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)))
  (q : τ (Obj (@AffineSpecBigSlice_cat R))) ⊢
  @comm_ring_psh_value
    (@AffineSpecBigSlice_cat R)
    (@ambient_affine_basis_psh K A U R i)
    q
  ≡ @comm_ring_psh_value
      (@Slice_cat K U)
      (@reflective_comm_ringed_site_slice_ambient_psh K A U)
      (@fapp0
        (@AffineSpecBigSlice_cat R)
        (@Slice_cat K U)
        i q);

// Both transparent record fields have exact constructor beta.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (R : τ CommRing)
  (X : τ (@AffineSchemePresentation R))
  (i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)))
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
      (@affine_scheme_underlying_psh R X))) ⊢
  @affine_basis_realization_semantics
    K A U P R X i
    (@affine_basis_realization_intro K A U P R X i basis bridge)
  ≡ basis;

assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (R : τ CommRing)
  (X : τ (@AffineSchemePresentation R))
  (i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)))
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
      (@affine_scheme_underlying_psh R X))) ⊢
  @affine_basis_realization_bridge
    K A U P R X i
    (@affine_basis_realization_intro K A U P R X i basis bridge)
  ≡ bridge;

// Derived coordinates are related by one whole composed DefIso.
assert [K : Cat]
  (A : τ (@ReflectiveCommRingedSite K))
  (U : τ (Obj K))
  (P : τ (@SuppliedReflectiveCommRingedSlicePresentation K A U))
  (R : τ CommRing)
  (X : τ (@AffineSchemePresentation R))
  (i : τ (Functor
      (@AffineSpecBigSlice_cat R)
      (@Slice_cat K U)))
  (Q : τ (@AffineBasisRealizationAlong K A U P R X i)) ⊢
  @affine_basis_realization_coordinate_defiso K A U P R X i Q
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@ambient_affine_basis_psh K A U R i)
      (@affine_spec_coordinate_psh R));
