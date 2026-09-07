/*
  Identity, extensionality, and composition of maps on actual whole kernels.
  All equations derive from the original universal uniqueness operation.
  These are theorem paths, not new runtime functoriality rewrites.
*/
require open emdash.emdash3_2_kernel_maps;
require open emdash.emdash3_2_hom_factor_composition;

symbol computational_kernel_map_identity_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  : τ (@= (Hom C (@computational_kernel_object C S A0 B0 d0 K0) (@computational_kernel_object C S A0 B0 d0 K0))
      (@computational_kernel_map C S A0 B0 A0 B0 d0 d0 K0 K0 (@id C A0) (@hom_precomp_factor_identity C A0 B0 d0))
      (@id C (@computational_kernel_object C S A0 B0 d0 K0)))
≔ @computational_kernel_map_unique_path
    C S A0 B0 A0 B0 d0 d0 K0 K0 (@id C A0) (@hom_precomp_factor_identity C A0 B0 d0)
    (@id C (@computational_kernel_object C S A0 B0 d0 K0))
    (@eq_refl (Hom C
          (@computational_kernel_object C S A0 B0 d0 K0) A0)
        (@computational_kernel_morphism C S A0 B0 d0 K0));

// The induced map depends only on the visible base component up to equality.
symbol computational_kernel_map_equal_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f g : τ (Hom C A0 A1))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 g)))
  (equal : τ (@= (Hom C A0 A1) f g))
  : τ
    (@= (Hom C
        (@computational_kernel_object C S A0 B0 d0 K0)
        (@computational_kernel_object C S A1 B1 d1 K1))
      (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F)
      (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 g G))
≔ @computational_kernel_map_unique_path C S A0 B0 A1 B1 d0 d1 K0 K1 f F
    (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 g G)
    (@eq_trans _ _ _ _
      (@computational_kernel_map_path C S A0 B0 A1 B1 d0 d1 K0 K1 g G)
      (@eq_ap (Hom C A0 A1)
        (Hom C (@computational_kernel_object C S A0 B0 d0 K0) A1)
        (λ h : τ (Hom C A0 A1),
          @comp_fapp0 C
            (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 h
            (@computational_kernel_morphism C S A0 B0 d0 K0))
        _ _ (@eq_sym _ _ _ equal)));

// Reconstruction of the composite at the original structural morphism.
symbol computational_kernel_map_composite_reconstruction
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  [A2 B2 : τ (Obj C)]
  (d2 : τ (Hom C A2 B2))
  (K2 : τ (@ComputationalKernel C S A2 B2 d2))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C A1 A2))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A1 B1 B2 d1 (@comp_fapp0 C A1 A2 B2 d2 g)))
  : τ (@= (Hom C (@computational_kernel_object C S A0 B0 d0 K0) A2)
      (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0)
          (@computational_kernel_object C S A2 B2 d2 K2) A2
          (@computational_kernel_morphism C S A2 B2 d2 K2)
          (@comp_fapp0 C
            (@computational_kernel_object C S A0 B0 d0 K0)
            (@computational_kernel_object C S A1 B1 d1 K1)
            (@computational_kernel_object C S A2 B2 d2 K2)
            (@computational_kernel_map C S A1 B1 A2 B2 d1 d2 K1 K2 g G)
            (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F)))
      (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0) A0 A2
          (@comp_fapp0 C A0 A1 A2 g f)
          (@computational_kernel_morphism C S A0 B0 d0 K0)))
≔ (@eq_trans _ _ _ _
      (@comp_assoc C
          (@computational_kernel_object C S A0 B0 d0 K0)
          (@computational_kernel_object C S A1 B1 d1 K1)
          (@computational_kernel_object C S A2 B2 d2 K2) A2
          (@computational_kernel_morphism C S A2 B2 d2 K2)
          (@computational_kernel_map C S A1 B1 A2 B2 d1 d2 K1 K2 g G)
          (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C
            (@computational_kernel_object C S A1 B1 d1 K1) A2) (Hom C
            (@computational_kernel_object C S A0 B0 d0 K0) A2)
        (λ h : τ (Hom C
              (@computational_kernel_object C S A1 B1 d1 K1) A2), @comp_fapp0 C
            (@computational_kernel_object C S A0 B0 d0 K0)
            (@computational_kernel_object C S A1 B1 d1 K1) A2 h
            (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F)) _ _
          (@computational_kernel_map_path C S A1 B1 A2 B2 d1 d2 K1 K2 g G))
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C
            (@computational_kernel_object C S A0 B0 d0 K0)
            (@computational_kernel_object C S A1 B1 d1 K1) A1 A2 g
            (@computational_kernel_morphism C S A1 B1 d1 K1)
            (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F)))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C
            (@computational_kernel_object C S A0 B0 d0 K0) A1) (Hom C
            (@computational_kernel_object C S A0 B0 d0 K0) A2)
        (λ h : τ (Hom C
              (@computational_kernel_object C S A0 B0 d0 K0) A1), @comp_fapp0 C
            (@computational_kernel_object C S A0 B0 d0 K0) A1 A2 g h) _ _
          (@computational_kernel_map_path C S A0 B0 A1 B1 d0 d1 K0 K1 f F))
      (@comp_assoc C
          (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 A2 g f
          (@computational_kernel_morphism C S A0 B0 d0 K0))))));

// The map of the pasted factor is the composite of the two selected maps.
symbol computational_kernel_map_composition_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  [A2 B2 : τ (Obj C)]
  (d2 : τ (Hom C A2 B2))
  (K2 : τ (@ComputationalKernel C S A2 B2 d2))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C A1 A2))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A1 B1 B2 d1 (@comp_fapp0 C A1 A2 B2 d2 g)))
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
        (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F)))
≔ @computational_kernel_map_unique_path C S A0 B0 A2 B2 d0 d2 K0 K2
  (@comp_fapp0 C A0 A1 A2 g f)
  (@hom_precomp_factor_paste C A0 B0 A1 B1 A2 B2 d0 d1 d2 f g F G)
    (@comp_fapp0 C
        (@computational_kernel_object C S A0 B0 d0 K0)
        (@computational_kernel_object C S A1 B1 d1 K1)
        (@computational_kernel_object C S A2 B2 d2 K2)
        (@computational_kernel_map C S A1 B1 A2 B2 d1 d2 K1 K2 g G)
        (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f F))
    (@computational_kernel_map_composite_reconstruction C S A0 B0 A1 B1 d0 d1 K0 K1 A2 B2 d2 K2 f g F G);
