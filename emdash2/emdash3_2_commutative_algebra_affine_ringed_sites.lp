/*
  Assumption-explicit affine reflective structure sheaves.

  The selected site is exactly the internally generated big-affine Zariski
  topology. A supplied reflective CommRing-valued sheaf theory and one sheaf
  object are retained together with a whole DefIso from its included
  presheaf to the computing coordinate presheaf.

  The whole comparison owns naturality and arrow action. Readable component
  observations merely project it at one affine-site object. This transparent
  module adds no rules and does not construct sheafification, prove
  localization locality or a stalk-local-ring condition, compare with the
  small site, or package a scheme.
*/

require open emdash.emdash3_2_ringed_sites;
require open emdash.emdash3_2_commutative_algebra_affine_zariski;

// Supplied reflective structure sheaf with a whole computing presentation.
symbol AffineStructureSheafPresentation
  (R : τ CommRing)
  : Grpd
≔ `Σ_ S : τ (@SheafificationCapability
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat),
   `Σ_ O : τ (Obj (@Sheaf_cat
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_big_zariski_topology R)
        CommRing_cat)),
      @DefIso
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
        (@affine_spec_coordinate_psh R);

// Constructor for the transparent presentation package.
symbol affine_structure_sheaf_intro
  [R : τ CommRing]
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
      (@affine_spec_coordinate_psh R)))
  : τ (@AffineStructureSheafPresentation R)
≔ @Struct_sigma
    (@SheafificationCapability
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat)
    (λ S0 : τ (@SheafificationCapability
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_big_zariski_topology R)
        CommRing_cat),
      `Σ_ O0 : τ (Obj (@Sheaf_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat)),
        @DefIso
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
              S0)
            O0)
          (@affine_spec_coordinate_psh R))
    S
    (@Struct_sigma
      (Obj (@Sheaf_cat
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_big_zariski_topology R)
        CommRing_cat))
      (λ O0 : τ (Obj (@Sheaf_cat
          (@AffineSpecBigSlice_cat R)
          (@affine_spec_big_zariski_topology R)
          CommRing_cat)),
        @DefIso
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
            O0)
          (@affine_spec_coordinate_psh R))
      O
      presentation);

// Selected supplied reflector capability.
symbol affine_structure_sheaf_sheafification
  [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R))
  : τ (@SheafificationCapability
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat)
≔ sigma_Fst P;

// Selected structure-sheaf object over the exact generated topology.
symbol affine_structure_sheaf_object
  [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R))
  : τ (Obj (@Sheaf_cat
      (@AffineSpecBigSlice_cat R)
      (@affine_spec_big_zariski_topology R)
      CommRing_cat))
≔ sigma_Fst (sigma_Snd P);

// The presentation determines a reflective commutative-ringed big site.
symbol affine_structure_sheaf_ringed_site
  [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R))
  : τ (@ReflectiveCommRingedSite (@AffineSpecBigSlice_cat R))
≔ @reflective_comm_ringed_site_intro
    (@AffineSpecBigSlice_cat R)
    (@affine_spec_big_zariski_topology R)
    (@affine_structure_sheaf_sheafification R P)
    (@affine_structure_sheaf_object R P);

// Underlying whole presheaf, routed through the ringed-site owner.
symbol affine_structure_sheaf_underlying_psh
  [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R))
  : τ (@CommRingPsh (@AffineSpecBigSlice_cat R))
≔ @reflective_comm_ringed_site_underlying_psh
    (@AffineSpecBigSlice_cat R)
    (@affine_structure_sheaf_ringed_site R P);

// Whole computational comparison with the computing coordinate presheaf.
symbol affine_structure_sheaf_coordinate_defiso
  [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R))
  : τ (@DefIso
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_structure_sheaf_underlying_psh R P)
      (@affine_spec_coordinate_psh R))
≔ sigma_Snd (sigma_Snd P);

// Component of the whole comparison at an arbitrary affine-site object.
symbol affine_structure_sheaf_to_coordinate_at
  [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R))
  (U : τ (Obj (@AffineSpecBigSlice_cat R)))
  : τ (@CommRingHom
      (@comm_ring_psh_value
        (@AffineSpecBigSlice_cat R)
        (@affine_structure_sheaf_underlying_psh R P)
        U)
      (@comm_ring_psh_value
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_coordinate_psh R)
        U))
≔ @tapp0_fapp0
    (Op_cat (@AffineSpecBigSlice_cat R))
    CommRing_cat
    (@affine_structure_sheaf_underlying_psh R P)
    (@affine_spec_coordinate_psh R)
    U
    (@defiso_to
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_structure_sheaf_underlying_psh R P)
      (@affine_spec_coordinate_psh R)
      (@affine_structure_sheaf_coordinate_defiso R P));

// Component of the whole inverse comparison at the same site object.
symbol affine_structure_sheaf_from_coordinate_at
  [R : τ CommRing]
  (P : τ (@AffineStructureSheafPresentation R))
  (U : τ (Obj (@AffineSpecBigSlice_cat R)))
  : τ (@CommRingHom
      (@comm_ring_psh_value
        (@AffineSpecBigSlice_cat R)
        (@affine_spec_coordinate_psh R)
        U)
      (@comm_ring_psh_value
        (@AffineSpecBigSlice_cat R)
        (@affine_structure_sheaf_underlying_psh R P)
        U))
≔ @tapp0_fapp0
    (Op_cat (@AffineSpecBigSlice_cat R))
    CommRing_cat
    (@affine_spec_coordinate_psh R)
    (@affine_structure_sheaf_underlying_psh R P)
    U
    (@defiso_from
      (@CommRingPsh_cat (@AffineSpecBigSlice_cat R))
      (@affine_structure_sheaf_underlying_psh R P)
      (@affine_spec_coordinate_psh R)
      (@affine_structure_sheaf_coordinate_defiso R P));
