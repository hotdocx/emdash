/* Actual kernel map consumers, laws, choice comparison, and endpoint guard. */
require open emdash.emdash3_2_kernel_map_isos;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  ⊢
    (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f factor) : τ (Hom C
      (@computational_kernel_object C S A0 B0 d0 K0)
      (@computational_kernel_object C S A1 B1 d1 K1));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  ⊢ @computational_kernel_map_path C S A0 B0 A1 B1 d0 d1 K0 K1 f factor : τ
    (@= (Hom C
        (@computational_kernel_object C S A0 B0 d0 K0) A1)
      (@comp_fapp0 C
        (@computational_kernel_object C S A0 B0 d0 K0)
        (@computational_kernel_object C S A1 B1 d1 K1) A1
        (@computational_kernel_morphism C S A1 B1 d1 K1)
        (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f factor))
      (@comp_fapp0 C
        (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 f
        (@computational_kernel_morphism C S A0 B0 d0 K0)));

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A0 B0 : τ (Obj C)) (d0 : τ (Hom C A0 B0))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  ⊢ @computational_kernel_map_identity_path C S A0 B0 d0 K0
  : τ
    (@= (Hom C
        (@computational_kernel_object C S A0 B0 d0 K0)
        (@computational_kernel_object C S A0 B0 d0 K0))
      (@computational_kernel_map C S A0 B0 A0 B0 d0 d0 K0 K0
        (@id C A0)
        (@hom_precomp_factor_identity C A0 B0 d0))
      (@id C
        (@computational_kernel_object C S A0 B0 d0 K0)));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (A2 B2 : τ (Obj C))
  (d2 : τ (Hom C A2 B2))
  (K2 : τ (@ComputationalKernel C S A2 B2 d2))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C A1 A2))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A1 B1 B2 d1 (@comp_fapp0 C A1 A2 B2 d2 g)))
  ⊢ @computational_kernel_map_composition_path C S A0 B0 A1 B1 d0 d1 K0 K1 A2 B2 d2 K2 f g F G
  : τ
    (@= (Hom C
        (@computational_kernel_object C S A0 B0 d0 K0)
        (@computational_kernel_object C S A2 B2 d2 K2))
      (@computational_kernel_map C S A0 B0 A2 B2 d0 d2 K0 K2
        (@comp_fapp0 C A0 A1 A2 g f)
        (@hom_precomp_factor_paste C A0 B0 A1 B1 A2 B2 d0 d1 d2 f g F G))
      (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0)
          (@computational_kernel_object C S A1 B1 d1 K1)
          (@computational_kernel_object C S A2 B2 d2 K2)
          (@computational_kernel_map C S A1 B1 A2 B2 d1 d2 K1 K2 g G)
          (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F)));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
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
  ⊢ @iso_evidence_to C
    (@computational_kernel_object C S A0 B0 d0 K0)
    (@computational_kernel_object C S A1 B1 d1 K1)
    (@computational_kernel_maps_iso C S A0 B0 A1 B1 d0 d1 K0 K1 f g F G inverse0 inverse1) ≡
    (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
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
  ⊢ @iso_evidence_from C
    (@computational_kernel_object C S A0 B0 d0 K0)
    (@computational_kernel_object C S A1 B1 d1 K1)
    (@computational_kernel_maps_iso C S A0 B0 A1 B1 d0 d1 K0 K1 f g F G inverse0 inverse1) ≡
    (@computational_kernel_map C S A1 B1 A0 B0 d1 d0 K1 K0 g G);

assertnot
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (other : τ (@ComputationalKernel C S A0 B0 d0))
  ⊢
    (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f factor) : τ (Hom C
      (@computational_kernel_object C S A0 B0 d0 other)
      (@computational_kernel_object C S A1 B1 d1 K1));

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A0 B0 : τ (Obj C)) (d0 : τ (Hom C A0 B0))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (other : τ (@ComputationalKernel C S A0 B0 d0))
  ⊢ @computational_kernel_maps_iso C S A0 B0 A0 B0 d0 d0 K0 other
      (@id C A0) (@id C A0)
      (@hom_precomp_factor_identity C A0 B0 d0)
      (@hom_precomp_factor_identity C A0 B0 d0)
      (@eq_refl (Hom C A0 A0) (@id C A0))
      (@eq_refl (Hom C A0 A0) (@id C A0))
  : τ
    (@IsoEvidence C
      (@computational_kernel_object C S A0 B0 d0 K0)
      (@computational_kernel_object C S A0 B0 d0 other));
