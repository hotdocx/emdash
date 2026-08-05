/*
  Reviewer-facing assumption-explicit affine reflective structure sheaves.

  The included structure sheaf is compared with the computing coordinate
  presheaf by a whole DefIso. Its components are observations of that whole
  comparison, not object-only replacement data. No localization-locality,
  stalk-local-ring, small-site, or scheme claim is made here.
*/

require open emdash.emdash3_2_commutative_algebra_affine_ringed_sites;

// catalog-area: Affine reflective structure-sheaf presentations
// Exactly the supplied reflector, sheaf object, and whole DefIso form one.
assert [R : τ CommRing]
  (S : τ (@SheafificationCapability
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat))
  (O : τ (Obj (@Sheaf_cat
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat)))
  (presentation : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@fapp0
        (@Sheaf_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat)
        (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
        (@sheaf_include_func
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat
          S)
        O)
      (@affine_spec_coordinate_psh R))) ⊢
  @affine_structure_sheaf_intro R S O presentation
  : τ (@AffineStructureSheafPresentation R);

// The two data projections compute through the transparent Sigma package.
assert [R : τ CommRing]
  (S : τ (@SheafificationCapability
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat))
  (O : τ (Obj (@Sheaf_cat
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat)))
  (presentation : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@fapp0
        (@Sheaf_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat)
        (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
        (@sheaf_include_func
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat
          S)
        O)
      (@affine_spec_coordinate_psh R))) ⊢
  @affine_structure_sheaf_sheafification R
    (@affine_structure_sheaf_intro R S O presentation)
  ≡ S;

assert [R : τ CommRing]
  (S : τ (@SheafificationCapability
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat))
  (O : τ (Obj (@Sheaf_cat
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat)))
  (presentation : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@fapp0
        (@Sheaf_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat)
        (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
        (@sheaf_include_func
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat
          S)
        O)
      (@affine_spec_coordinate_psh R))) ⊢
  @affine_structure_sheaf_object R
    (@affine_structure_sheaf_intro R S O presentation)
  ≡ O;

// The resulting ringed site carries exactly the generated big topology.
assert [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R)) ⊢
  @reflective_comm_ringed_site_topology
    (@AffineSpecBigSlice_cat R)
    (@affine_structure_sheaf_ringed_site R P)
  ≡ @affine_spec_big_zariski_topology R;

// Its included structure is one whole CommRing-valued presheaf.
assert [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R)) ⊢
  @affine_structure_sheaf_underlying_psh R P
  : τ (@CommRingPsh (@AffineSpecBigSlice_cat R));

// The selected presentation is a whole computational isomorphism.
assert [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R)) ⊢
  @affine_structure_sheaf_coordinate_defiso R P
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_structure_sheaf_underlying_psh R P)
      (@affine_spec_coordinate_psh R));

// Generic DefIso cancellation computes at whole-presheaf level.
assert [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R)) ⊢
  @comp_fapp0
    (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
    (@affine_structure_sheaf_underlying_psh R P)
    (@affine_spec_coordinate_psh R)
    (@affine_structure_sheaf_underlying_psh R P)
    (@defiso_from
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_structure_sheaf_underlying_psh R P)
      (@affine_spec_coordinate_psh R)
      (@affine_structure_sheaf_coordinate_defiso R P))
    (@defiso_to
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_structure_sheaf_underlying_psh R P)
      (@affine_spec_coordinate_psh R)
      (@affine_structure_sheaf_coordinate_defiso R P))
  ≡ @id
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_structure_sheaf_underlying_psh R P);

// At a literal chart, the coordinate endpoint computes to its ring S.
assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (P : τ (@AffineStructureSheafPresentation R)) ⊢
  @affine_structure_sheaf_to_coordinate_at
    R P (@affine_spec_chart R S h)
  : τ (@CommRingHom
      (@comm_ring_psh_value
        (@AffineSpecBigSlice_cat R)
        (@affine_structure_sheaf_underlying_psh R P)
        (@affine_spec_chart R S h))
      S);

assert [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (P : τ (@AffineStructureSheafPresentation R)) ⊢
  @affine_structure_sheaf_from_coordinate_at
    R P (@affine_spec_chart R S h)
  : τ (@CommRingHom
      S
      (@comm_ring_psh_value
        (@AffineSpecBigSlice_cat R)
        (@affine_structure_sheaf_underlying_psh R P)
        (@affine_spec_chart R S h)));
