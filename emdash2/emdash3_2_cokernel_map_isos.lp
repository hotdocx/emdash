/*
  Inverse base components induce inverse maps on the actual cokernels.
  Both compatibility factors remain explicit internal Hom-fibre points.
*/
require open emdash.emdash3_2_cokernel_map_laws;
require open emdash.emdash3_2_iso_evidence_constructors;

symbol computational_cokernel_maps_inverse_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (Q0 : τ (@ComputationalCokernel C S A0 B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A1 B1 d1))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B0))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A0 B0 A1 d0 (@comp_fapp0 C A1 B1 B0 g d1)))
  (inverse : τ (@= (Hom C B0 B0) (@comp_fapp0 C B0 B1 B0 g f) (@id C B0)))
  : τ (@= (Hom C (@computational_cokernel_object C S A0 B0 d0 Q0) (@computational_cokernel_object C S A0 B0 d0 Q0))
      (@comp_fapp0 C
          (@computational_cokernel_object C S A0 B0 d0 Q0)
          (@computational_cokernel_object C S A1 B1 d1 Q1)
          (@computational_cokernel_object C S A0 B0 d0 Q0)
          (@computational_cokernel_map C S A1 B1 A0 B0 d1 d0 Q1 Q0 g G)
          (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F))
      (@id C (@computational_cokernel_object C S A0 B0 d0 Q0)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@computational_cokernel_map_composition_path
        C S A0 B0 A1 B1 d0 d1 Q0 Q1 A0 B0 d0 Q0 f g F G))
    (@eq_trans _ _ _ _
      (@computational_cokernel_map_equal_path
        C S A0 B0 A0 B0 d0 d0 Q0 Q0
        (@comp_fapp0 C B0 B1 B0 g f)
          (@id C B0)
          (@hom_postcomp_factor_paste C A0 B0 A1 B1 A0 B0 d0 d1 d0 f g F G)
          (@hom_postcomp_factor_identity C A0 B0 d0) inverse)
      (@computational_cokernel_map_identity_path C S A0 B0 d0 Q0));

// Package the already-constructed maps and both derived inverse equations.
symbol computational_cokernel_maps_iso
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 : τ (Obj C)]
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
  : τ
    (@IsoEvidence C
      (@computational_cokernel_object C S A0 B0 d0 Q0)
      (@computational_cokernel_object C S A1 B1 d1 Q1))
≔ @iso_evidence_intro C
  (@computational_cokernel_object C S A0 B0 d0 Q0)
  (@computational_cokernel_object C S A1 B1 d1 Q1)
    (@computational_cokernel_map C S A0 B0 A1 B1 d0 d1 Q0 Q1 f F)
      (@computational_cokernel_map C S A1 B1 A0 B0 d1 d0 Q1 Q0 g G)
    (@computational_cokernel_maps_inverse_path
      C S A0 B0 A1 B1 d0 d1 Q0 Q1 f g F G inverse0)
    (@computational_cokernel_maps_inverse_path
      C S A1 B1 A0 B0 d1 d0 Q1 Q0 g f G F inverse1);
