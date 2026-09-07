/*
  Identity, extensionality, and composition of maps on actual whole cokernels.
  All equations derive from the original universal uniqueness operation.
  These are theorem paths, not new runtime functoriality rewrites.
*/
require open emdash.emdash3_2_cokernel_maps;
require open emdash.emdash3_2_hom_factor_composition;

symbol computational_cokernel_map_identity_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  : τ (@= (Hom C (@computational_cokernel_object C S A0 B0 d0 Q0) (@computational_cokernel_object C S A0 B0 d0 Q0))
      (@computational_cokernel_map C S A0 B0 A0 B0 d0 d0 Q0 Q0
          (@id C B0)
          (@hom_postcomp_factor_identity C A0 B0 d0))
      (@id C (@computational_cokernel_object C S A0 B0 d0 Q0)))
≔ @computational_cokernel_map_unique_path
    C S A0 B0 A0 B0 d0 d0 Q0 Q0 (@id C B0) (@hom_postcomp_factor_identity C A0 B0 d0)
    (@id C (@computational_cokernel_object C S A0 B0 d0 Q0))
    (@eq_refl (Hom C B0
          (@computational_cokernel_object C S A0 B0 d0 Q0))
        (@computational_cokernel_morphism C S A0 B0 d0 Q0));

// The induced map depends only on the visible base component up to equality.
symbol computational_cokernel_map_equal_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f g : τ (Hom C B0 B1))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 g d0)))
  (equal : τ (@= (Hom C B0 B1) f g))
  : τ
    (@= (Hom C
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A1 B1 d1 Q1))
      (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F)
      (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 g G))
≔ @computational_cokernel_map_unique_path C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F
    (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 g G)
    (@eq_trans _ _ _ _
      (@computational_cokernel_map_path C S A0 B0 A1 B1 d0 d1 Q0 Q1 g G)
      (@eq_ap (Hom C B0 B1)
        (Hom C B0 (@computational_cokernel_object C S A1 B1 d1 Q1))
        (λ h : τ (Hom C B0 B1),
          @comp_fapp0 C B0 B1
            (@computational_cokernel_object C S A1 B1 d1 Q1)
            (@computational_cokernel_morphism C S A1 B1 d1 Q1) h)
        _ _ (@eq_sym _ _ _ equal)));

// Reconstruction of the composite at the original structural morphism.
symbol computational_cokernel_map_composite_reconstruction
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  [A2 B2 : τ (Obj C)]
  (d2 : τ (Hom C A2 B2))
  (Q2 : τ (@ComputationalCokernel C S A2 B2 d2))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B2))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A2 B2 A1 d2 (@comp_fapp0 C A1 B1 B2 g d1)))
  : τ (@= (Hom C B0 (@computational_cokernel_object C S A2 B2 d2 Q2))
      (@comp_fapp0 C B0
          (@computational_cokernel_object C S A0 B0 d0 Q0)
          (@computational_cokernel_object C S A2 B2 d2 Q2)
          (@comp_fapp0 C
            (@computational_cokernel_object C S A0 B0 d0 Q0)
            (@computational_cokernel_object C S A1 B1 d1 Q1)
            (@computational_cokernel_object C S A2 B2 d2 Q2)
            (@computational_cokernel_map C S A1 B1 A2 B2 d1 d2 Q1 Q2 g G)
            (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F))
          (@computational_cokernel_morphism C S A0 B0 d0 Q0))
      (@comp_fapp0 C B0 B2
          (@computational_cokernel_object C S A2 B2 d2 Q2)
          (@computational_cokernel_morphism C S A2 B2 d2 Q2)
          (@comp_fapp0 C B0 B1 B2 g f)))
≔ (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C B0
            (@computational_cokernel_object C S A0 B0 d0 Q0)
            (@computational_cokernel_object C S A1 B1 d1 Q1)
            (@computational_cokernel_object C S A2 B2 d2 Q2)
            (@computational_cokernel_map C S A1 B1 A2 B2 d1 d2 Q1 Q2 g G)
            (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F)
            (@computational_cokernel_morphism C S A0 B0 d0 Q0)))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C B0
            (@computational_cokernel_object C S A1 B1 d1 Q1)) (Hom C B0
            (@computational_cokernel_object C S A2 B2 d2 Q2))
        (λ h : τ (Hom C B0
              (@computational_cokernel_object C S A1 B1 d1 Q1)), @comp_fapp0 C B0
            (@computational_cokernel_object C S A1 B1 d1 Q1)
            (@computational_cokernel_object C S A2 B2 d2 Q2)
            (@computational_cokernel_map C S A1 B1 A2 B2 d1 d2 Q1 Q2 g G) h) _ _
          (@computational_cokernel_map_path C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F))
      (@eq_trans _ _ _ _
      (@comp_assoc C B0 B1
          (@computational_cokernel_object C S A1 B1 d1 Q1)
          (@computational_cokernel_object C S A2 B2 d2 Q2)
          (@computational_cokernel_map C S A1 B1 A2 B2 d1 d2 Q1 Q2 g G)
          (@computational_cokernel_morphism C S A1 B1 d1 Q1) f)
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C B1
            (@computational_cokernel_object C S A2 B2 d2 Q2)) (Hom C B0
            (@computational_cokernel_object C S A2 B2 d2 Q2))
        (λ h : τ (Hom C B1
              (@computational_cokernel_object C S A2 B2 d2 Q2)), @comp_fapp0 C B0 B1
            (@computational_cokernel_object C S A2 B2 d2 Q2) h f) _ _
          (@computational_cokernel_map_path C S A1 B1 A2 B2 d1 d2 Q1 Q2 g G))
      (@eq_sym _ _ _
          (@comp_assoc C B0 B1 B2
            (@computational_cokernel_object C S A2 B2 d2 Q2)
            (@computational_cokernel_morphism C S A2 B2 d2 Q2) g f))))));

// The map of the pasted factor is the composite of the two selected maps.
symbol computational_cokernel_map_composition_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  [A2 B2 : τ (Obj C)]
  (d2 : τ (Hom C A2 B2))
  (Q2 : τ (@ComputationalCokernel C S A2 B2 d2))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B2))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A2 B2 A1 d2 (@comp_fapp0 C A1 B1 B2 g d1)))
  : τ
    (@= (Hom C
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A2 B2 d2 Q2))
      (@computational_cokernel_map C S A0 B0 A2 B2 d0 d2 Q0 Q2
        (@comp_fapp0 C B0 B1 B2 g f)
        (@hom_postcomp_factor_paste C A0 B0 A1 B1 A2 B2 d0 d1 d2 f g F G))
      (@comp_fapp0 C
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A1 B1 d1 Q1)
        (@computational_cokernel_object C S A2 B2 d2 Q2)
        (@computational_cokernel_map C S A1 B1 A2 B2 d1 d2 Q1 Q2 g G)
        (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F)))
≔ @computational_cokernel_map_unique_path C S A0 B0 A2 B2 d0 d2 Q0 Q2
  (@comp_fapp0 C B0 B1 B2 g f)
  (@hom_postcomp_factor_paste C A0 B0 A1 B1 A2 B2 d0 d1 d2 f g F G)
    (@comp_fapp0 C
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A1 B1 d1 Q1)
        (@computational_cokernel_object C S A2 B2 d2 Q2)
        (@computational_cokernel_map C S A1 B1 A2 B2 d1 d2 Q1 Q2 g G)
        (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F))
    (@computational_cokernel_map_composite_reconstruction C S A0 B0 A1 B1 d0 d1 Q0 Q1 A2 B2 d2 Q2 f g F G);
