/*
  Maps between actual whole cokernels from an internal postcomposition factor.

  The factor of f ∘ d0 through d1 supplies the upper component. Its path
  derives the quotient test; source cokernel universality constructs the map.
*/
require open emdash.emdash3_2_kernels_cokernels;
require open emdash.emdash3_2_hom_factor_spaces;

// The target projection after the base map kills the source differential.
symbol computational_cokernel_map_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  : τ (@= (Hom C A0 (@computational_cokernel_object C S A1 B1 d1 Q1))
      (@comp_fapp0 C A0 B0
          (@computational_cokernel_object C S A1 B1 d1 Q1)
          (@comp_fapp0 C B0 B1
            (@computational_cokernel_object C S A1 B1 d1 Q1)
            (@computational_cokernel_morphism C S A1 B1 d1 Q1) f) d0)
      (@preadditive_hom_zero C S A0 (@computational_cokernel_object C S A1 B1 d1 Q1)))
≔ (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C A0 B0 B1
            (@computational_cokernel_object C S A1 B1 d1 Q1)
            (@computational_cokernel_morphism C S A1 B1 d1 Q1) f d0))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A0 B1) (Hom C A0 (@computational_cokernel_object C S A1 B1 d1 Q1))
        (λ h : τ (Hom C A0 B1), @comp_fapp0 C A0 B1
            (@computational_cokernel_object C S A1 B1 d1 Q1)
            (@computational_cokernel_morphism C S A1 B1 d1 Q1) h)
        _ _ (@eq_sym _ _ _ (@hom_postcomp_factor_path C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0) factor)))
      (@eq_trans _ _ _ _
      (@comp_assoc C A0 A1 B1
          (@computational_cokernel_object C S A1 B1 d1 Q1)
          (@computational_cokernel_morphism C S A1 B1 d1 Q1) d1
          (@hom_postcomp_factor_arrow C A1 B1 A0 d1
            (@comp_fapp0 C A0 B0 B1 f d0) factor))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A1
            (@computational_cokernel_object C S A1 B1 d1 Q1)) (Hom C A0
            (@computational_cokernel_object C S A1 B1 d1 Q1))
        (λ h : τ (Hom C A1
              (@computational_cokernel_object C S A1 B1 d1 Q1)), @comp_fapp0 C A0 A1
            (@computational_cokernel_object C S A1 B1 d1 Q1) h
            (@hom_postcomp_factor_arrow C A1 B1 A0 d1
              (@comp_fapp0 C A0 B0 B1 f d0) factor))
        _ _ (@computational_cokernel_annihilation C S A1 B1 d1 Q1))
      (@preadditive_comp_zero_left_path C S A0 A1
          (@computational_cokernel_object C S A1 B1 d1 Q1)
          (@hom_postcomp_factor_arrow C A1 B1 A0 d1
            (@comp_fapp0 C A0 B0 B1 f d0) factor))))));

// The source coannihilator point is derived from the upper Hom factor.
symbol computational_cokernel_map_cocone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  : τ (@CokernelCoannihilator C S A0 B0 d0 (@computational_cokernel_object C S A1 B1 d1 Q1))
≔ @Struct_sigma (Hom C B0 (@computational_cokernel_object C S A1 B1 d1 Q1))
    (λ h : τ (Hom C B0 (@computational_cokernel_object C S A1 B1 d1 Q1)),
      @= (Hom C A0
          (@computational_cokernel_object C S A1 B1 d1 Q1))
        (@comp_fapp0 C A0 B0
          (@computational_cokernel_object C S A1 B1 d1 Q1) h d0)
        (@preadditive_hom_zero C S A0 (@computational_cokernel_object C S A1 B1 d1 Q1)))
    (@comp_fapp0 C B0 B1
        (@computational_cokernel_object C S A1 B1 d1 Q1)
        (@computational_cokernel_morphism C S A1 B1 d1 Q1) f)
    (@computational_cokernel_map_zero_path C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor);

// Select the map from the actual source cokernel's contractible factor space.
symbol computational_cokernel_map
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  : τ (Hom C (@computational_cokernel_object C S A0 B0 d0 Q0) (@computational_cokernel_object C S A1 B1 d1 Q1))
≔ @computational_cokernel_colift C S A0 B0 d0 Q0
  (@computational_cokernel_object C S A1 B1 d1 Q1)
  (@computational_cokernel_map_cocone C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor);

// Reconstruction after the actual source cokernel projection.
symbol computational_cokernel_map_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  : τ (@= (Hom C B0 (@computational_cokernel_object C S A1 B1 d1 Q1))
      (@comp_fapp0 C B0
          (@computational_cokernel_object C S A0 B0 d0 Q0)
          (@computational_cokernel_object C S A1 B1 d1 Q1)
          (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor)
          (@computational_cokernel_morphism C S A0 B0 d0 Q0))
      (@comp_fapp0 C B0 B1
          (@computational_cokernel_object C S A1 B1 d1 Q1)
          (@computational_cokernel_morphism C S A1 B1 d1 Q1) f))
≔ @computational_cokernel_colift_path C S A0 B0 d0 Q0
  (@computational_cokernel_object C S A1 B1 d1 Q1)
  (@computational_cokernel_map_cocone C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor);

// Equality of actual maps follows from the original contractible factor space.
symbol computational_cokernel_map_unique_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (other : τ (Hom C
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A1 B1 d1 Q1)))
  (path : τ (@= (Hom C B0 (@computational_cokernel_object C S A1 B1 d1 Q1))
    (@comp_fapp0 C B0
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A1 B1 d1 Q1) other
        (@computational_cokernel_morphism C S A0 B0 d0 Q0))
      (@comp_fapp0 C B0 B1
        (@computational_cokernel_object C S A1 B1 d1 Q1)
        (@computational_cokernel_morphism C S A1 B1 d1 Q1) f)))
  : τ
    (@= (Hom C
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A1 B1 d1 Q1))
      (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor) other)
≔ @computational_cokernel_colift_unique_path C S A0 B0 d0 Q0
  (@computational_cokernel_object C S A1 B1 d1 Q1)
  (@computational_cokernel_map_cocone C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor) other path;
