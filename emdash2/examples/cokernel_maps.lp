/* Actual cokernel map consumers, laws, choice comparison, and endpoint guard. */
require open emdash.emdash3_2_cokernel_map_isos;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  ⊢
    (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor) : τ (Hom C
      (@computational_cokernel_object C S A0 B0 d0 Q0)
      (@computational_cokernel_object C S A1 B1 d1 Q1));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  ⊢ @computational_cokernel_map_path C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor : τ
    (@= (Hom C B0
        (@computational_cokernel_object C S A1 B1 d1 Q1))
      (@comp_fapp0 C B0
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A1 B1 d1 Q1)
        (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor)
        (@computational_cokernel_morphism C S A0 B0 d0 Q0))
      (@comp_fapp0 C B0 B1
        (@computational_cokernel_object C S A1 B1 d1 Q1)
        (@computational_cokernel_morphism C S A1 B1 d1 Q1) f));

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A0 B0 : τ (Obj C)) (d0 : τ (Hom C A0 B0))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  ⊢ @computational_cokernel_map_identity_path C S A0 B0 d0 Q0
  : τ
    (@= (Hom C
        (@computational_cokernel_object C S A0 B0 d0 Q0)
        (@computational_cokernel_object C S A0 B0 d0 Q0))
      (@computational_cokernel_map C S A0 B0 A0 B0 d0 d0 Q0 Q0
        (@id C B0)
        (@hom_postcomp_factor_identity C A0 B0 d0))
      (@id C
        (@computational_cokernel_object C S A0 B0 d0 Q0)));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (A2 B2 : τ (Obj C))
  (d2 : τ (Hom C A2 B2))
  (Q2 : τ (@ComputationalCokernel C S A2 B2 d2))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B2))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A2 B2 A1 d2 (@comp_fapp0 C A1 B1 B2 g d1)))
  ⊢ @computational_cokernel_map_composition_path C S A0 B0 A1 B1 d0 d1 Q0 Q1 A2 B2 d2 Q2 f g F G
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
          (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F)));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B0))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A0 B0 A1 d0 (@comp_fapp0 C A1 B1 B0 g d1)))
  (inverse0 : τ (@= (Hom C B0 B0) (@comp_fapp0 C B0 B1 B0 g f) (@id C B0)))
  (inverse1 : τ (@= (Hom C B1 B1) (@comp_fapp0 C B1 B0 B1 f g) (@id C B1)))
  ⊢ @iso_evidence_to C
    (@computational_cokernel_object C S A0 B0 d0 Q0)
    (@computational_cokernel_object C S A1 B1 d1 Q1)
    (@computational_cokernel_maps_iso C S A0 B0 A1 B1 d0 d1 Q0 Q1 f g F G inverse0 inverse1) ≡
    (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B0))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A0 B0 A1 d0 (@comp_fapp0 C A1 B1 B0 g d1)))
  (inverse0 : τ (@= (Hom C B0 B0) (@comp_fapp0 C B0 B1 B0 g f) (@id C B0)))
  (inverse1 : τ (@= (Hom C B1 B1) (@comp_fapp0 C B1 B0 B1 f g) (@id C B1)))
  ⊢ @iso_evidence_from C
    (@computational_cokernel_object C S A0 B0 d0 Q0)
    (@computational_cokernel_object C S A1 B1 d1 Q1)
    (@computational_cokernel_maps_iso C S A0 B0 A1 B1 d0 d1 Q0 Q1 f g F G inverse0 inverse1) ≡
    (@computational_cokernel_map C S A1 B1 A0 B0 d1 d0 Q1 Q0 g G);

assertnot
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 A1 B1 : τ (Obj C))
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (other : τ (@ComputationalCokernel C S A0 B0 d0))
  ⊢
    (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f factor) : τ (Hom C
      (@computational_cokernel_object C S A0 B0 d0 other)
      (@computational_cokernel_object C S A1 B1 d1 Q1));

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A0 B0 : τ (Obj C)) (d0 : τ (Hom C A0 B0))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (other : τ (@ComputationalCokernel C S A0 B0 d0))
  ⊢ @computational_cokernel_maps_iso C S A0 B0 A0 B0 d0 d0 Q0 other
      (@id C B0) (@id C B0)
      (@hom_postcomp_factor_identity C A0 B0 d0)
      (@hom_postcomp_factor_identity C A0 B0 d0)
      (@eq_refl (Hom C B0 B0) (@id C B0))
      (@eq_refl (Hom C B0 B0) (@id C B0))
  : τ
    (@IsoEvidence C
      (@computational_cokernel_object C S A0 B0 d0 Q0)
      (@computational_cokernel_object C S A0 B0 d0 other));
