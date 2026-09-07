/*
  Generic induced maps on the actual selected homology objects.

  The derived cycle map and boundary factor feed the generic cokernel map.
  Source and target are the original whole homology values, with no endpoint
  transport or extra agreement input.
*/
require open emdash.emdash3_2_homology_cycle_maps;
require open emdash.emdash3_2_cokernel_maps;

// The selected quotient map between the actual two boundary cokernels.
symbol computational_homology_map
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom C
      (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
≔ @computational_cokernel_map C
  (@computational_homology_preadditive C P t PA) A0
  (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A1
  (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_cokernel C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
  (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F);

// H(F) ∘ q0 = q1 ∘ Z(F), at the original homology projections.
symbol computational_homology_map_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  : τ
    (@= (Hom C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
          (@computational_homology_projection C P t PA A0 B0 D0 p0 H0))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_projection C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)))
≔ @computational_cokernel_map_path C
  (@computational_homology_preadditive C P t PA) A0
  (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A1
  (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_cokernel C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
  (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F);

// The original source cokernel's uniqueness applies without rebuilding it.
symbol computational_homology_map_unique_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  (other : τ (Hom C
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1)))
  (path : τ
      (@= (Hom C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
    (@comp_fapp0 C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1) other
        (@computational_homology_projection C P t PA A0 B0 D0 p0 H0))
    (@comp_fapp0 C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_projection C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F))))
  : τ
    (@= (Hom C
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
      (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F) other)
≔ @computational_cokernel_map_unique_path C
  (@computational_homology_preadditive C P t PA) A0
  (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A1
  (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_cokernel C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
  (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F) other path;
