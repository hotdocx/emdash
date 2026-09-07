/*
  Maps between actual whole kernels from an internal precomposition factor.

  The factor of d1 ∘ f through d0 supplies the lower component. Its path
  derives the cycle test; target kernel universality constructs the map.
*/
require open emdash.emdash3_2_kernels_cokernels;
require open emdash.emdash3_2_hom_factor_spaces;

// d1 ∘ (f ∘ k0) = 0, derived from the factor and source annihilation.
symbol computational_kernel_map_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  : τ (@= (Hom C (@computational_kernel_object C S A0 B0 d0 K0) B1)
      (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0) A1 B1 d1
          (@comp_fapp0 C
            (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 f
            (@computational_kernel_morphism C S A0 B0 d0 K0)))
      (@preadditive_hom_zero C S (@computational_kernel_object C S A0 B0 d0 K0) B1))
≔ (@eq_trans _ _ _ _
      (@comp_assoc C
          (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 B1 d1 f
          (@computational_kernel_morphism C S A0 B0 d0 K0))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A0 B1) (Hom C (@computational_kernel_object C S A0 B0 d0 K0) B1)
        (λ h : τ (Hom C A0 B1), @comp_fapp0 C
            (@computational_kernel_object C S A0 B0 d0 K0) A0 B1 h
            (@computational_kernel_morphism C S A0 B0 d0 K0))
        _ _ (@eq_sym _ _ _ (@hom_precomp_factor_path C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f) factor)))
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C
            (@computational_kernel_object C S A0 B0 d0 K0) A0 B0 B1
            (@hom_precomp_factor_arrow C A0 B0 B1 d0
              (@comp_fapp0 C A0 A1 B1 d1 f) factor) d0
            (@computational_kernel_morphism C S A0 B0 d0 K0)))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C
            (@computational_kernel_object C S A0 B0 d0 K0) B0) (Hom C
            (@computational_kernel_object C S A0 B0 d0 K0) B1)
        (λ h : τ (Hom C
              (@computational_kernel_object C S A0 B0 d0 K0) B0), @comp_fapp0 C
            (@computational_kernel_object C S A0 B0 d0 K0) B0 B1
            (@hom_precomp_factor_arrow C A0 B0 B1 d0
              (@comp_fapp0 C A0 A1 B1 d1 f) factor) h)
        _ _ (@computational_kernel_annihilation C S A0 B0 d0 K0))
      (@preadditive_comp_zero_right_path C S
          (@computational_kernel_object C S A0 B0 d0 K0) B0 B1
          (@hom_precomp_factor_arrow C A0 B0 B1 d0
            (@comp_fapp0 C A0 A1 B1 d1 f) factor))))));

// The target annihilator point is derived from the lower Hom factor.
symbol computational_kernel_map_cone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  : τ (@WeakKernelAnnihilator C S A1 B1 d1 (@computational_kernel_object C S A0 B0 d0 K0))
≔ @Struct_sigma (Hom C (@computational_kernel_object C S A0 B0 d0 K0) A1)
    (λ h : τ (Hom C (@computational_kernel_object C S A0 B0 d0 K0) A1),
      @= (Hom C
          (@computational_kernel_object C S A0 B0 d0 K0) B1)
        (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0) A1 B1 d1 h)
        (@preadditive_hom_zero C S (@computational_kernel_object C S A0 B0 d0 K0) B1))
    (@comp_fapp0 C
        (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 f
        (@computational_kernel_morphism C S A0 B0 d0 K0))
    (@computational_kernel_map_zero_path C S A0 B0 A1 B1 d0 d1 K0 K1 f factor);

// Select the map from the actual target kernel's contractible factor space.
symbol computational_kernel_map
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  : τ (Hom C (@computational_kernel_object C S A0 B0 d0 K0) (@computational_kernel_object C S A1 B1 d1 K1))
≔ @computational_kernel_lift C S A1 B1 d1 K1
  (@computational_kernel_object C S A0 B0 d0 K0)
  (@computational_kernel_map_cone C S A0 B0 A1 B1 d0 d1 K0 K1 f factor);

// Reconstruction after the actual target kernel embedding.
symbol computational_kernel_map_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  : τ (@= (Hom C (@computational_kernel_object C S A0 B0 d0 K0) A1)
      (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0)
          (@computational_kernel_object C S A1 B1 d1 K1) A1
          (@computational_kernel_morphism C S A1 B1 d1 K1)
          (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f factor))
      (@comp_fapp0 C
          (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 f
          (@computational_kernel_morphism C S A0 B0 d0 K0)))
≔ @computational_kernel_lift_path C S A1 B1 d1 K1
  (@computational_kernel_object C S A0 B0 d0 K0)
  (@computational_kernel_map_cone C S A0 B0 A1 B1 d0 d1 K0 K1 f factor);

// Equality of actual maps follows from the original contractible factor space.
symbol computational_kernel_map_unique_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (K0 : τ (@ComputationalKernel C S A0 B0 d0))
  (K1 : τ (@ComputationalKernel C S A1 B1 d1))
  (f : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (other : τ (Hom C (@computational_kernel_object C S A0 B0 d0 K0) (@computational_kernel_object C S A1 B1 d1 K1)))
  (path : τ (@= (Hom C (@computational_kernel_object C S A0 B0 d0 K0) A1)
    (@comp_fapp0 C
        (@computational_kernel_object C S A0 B0 d0 K0)
        (@computational_kernel_object C S A1 B1 d1 K1) A1
        (@computational_kernel_morphism C S A1 B1 d1 K1) other)
      (@comp_fapp0 C
        (@computational_kernel_object C S A0 B0 d0 K0) A0 A1 f
        (@computational_kernel_morphism C S A0 B0 d0 K0))))
  : τ
    (@= (Hom C
        (@computational_kernel_object C S A0 B0 d0 K0)
        (@computational_kernel_object C S A1 B1 d1 K1))
      (@computational_kernel_map C S A0 B0 A1 B1 d0 d1 K0 K1 f factor) other)
≔ @computational_kernel_lift_unique_path C S A1 B1 d1 K1
  (@computational_kernel_object C S A0 B0 d0 K0)
  (@computational_kernel_map_cone C S A0 B0 A1 B1 d0 d1 K0 K1 f factor) other path;
