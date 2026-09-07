/*
  Inverse base components induce inverse maps on the actual kernels.
  Both compatibility factors remain explicit internal Hom-fibre points.
*/
require open emdash.emdash3_2_kernel_map_laws;
require open emdash.emdash3_2_iso_evidence_constructors;

symbol computational_kernel_maps_inverse_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C A1 A0))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A1 B1 B0 d1 (@comp_fapp0 C A1 A0 B0 d0 g)))
  (inverse : τ (@= (Hom C A0 A0) (@comp_fapp0 C A0 A1 A0 g f) (@id C A0)))
  : τ (@= (Hom C (@computational_kernel_object C S A0 B0 d0 K0) (@computational_kernel_object C S A0 B0 d0 K0))
      (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0)
          (@computational_kernel_object C S A1 B1 d1 K1)
          (@computational_kernel_object C S A0 B0 d0 K0)
          (@computational_kernel_map C S A1 B1 A0 B0 d1 d0 K1 K0 g G)
          (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F))
      (@id C (@computational_kernel_object C S A0 B0 d0 K0)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@computational_kernel_map_composition_path
        C S A0 B0 A1 B1 d0 d1 K0 K1 A0 B0 d0 K0 f g F G))
    (@eq_trans _ _ _ _
      (@computational_kernel_map_equal_path
        C S A0 B0 A0 B0 d0 d0 K0 K0
        (@comp_fapp0 C A0 A1 A0 g f)
          (@id C A0)
          (@hom_precomp_factor_paste C A0 B0 A1 B1 A0 B0 d0 d1 d0 f g F G)
          (@hom_precomp_factor_identity C A0 B0 d0) inverse)
      (@computational_kernel_map_identity_path C S A0 B0 d0 K0));

// Package the already-constructed maps and both derived inverse equations.
symbol computational_kernel_maps_iso
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C A1 A0))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A1 B1 B0 d1 (@comp_fapp0 C A1 A0 B0 d0 g)))
  (inverse0 : τ (@= (Hom C A0 A0) (@comp_fapp0 C A0 A1 A0 g f) (@id C A0)))
  (inverse1 : τ (@= (Hom C A1 A1) (@comp_fapp0 C A1 A0 A1 f g) (@id C A1)))
  : τ
    (@IsoEvidence C
      (@computational_kernel_object C S A0 B0 d0 K0)
      (@computational_kernel_object C S A1 B1 d1 K1))
≔ @iso_evidence_intro C
  (@computational_kernel_object C S A0 B0 d0 K0)
  (@computational_kernel_object C S A1 B1 d1 K1)
    (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F)
      (@computational_kernel_map C S A1 B1 A0 B0 d1 d0 K1 K0 g G)
    (@computational_kernel_maps_inverse_path
      C S A0 B0 A1 B1 d0 d1 K0 K1 f g F G inverse0)
    (@computational_kernel_maps_inverse_path
      C S A1 B1 A0 B0 d1 d0 K1 K0 g f G F inverse1);
