/* A factor after an epic cover supplies the existing normal-mono test. */
require open emdash.emdash3_2_hom_factor_spaces;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

// The selected cokernel kills h after e, hence kills h by epic cancellation.
symbol normal_mono_test_from_epic_factor
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B X Y : τ (Obj C)]
  (m : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B m))
  (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (h : τ (Hom C X B))
  (covered : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  : τ (@NormalMonoTest C S A B m W X)
≔ @Struct_sigma (Hom C X B)
    (λ f : τ (Hom C X B), @= (Hom C X (@computational_cokernel_object C S A B m W))
      (@comp_fapp0 C X B (@computational_cokernel_object C S A B m W)
        (@computational_cokernel_morphism C S A B m W) f)
      (@preadditive_hom_zero C S X (@computational_cokernel_object C S A B m W)))
    h
    (@epic_precomposition_zero_to_zero_path C S Y X
      (@computational_cokernel_object C S A B m W) e epic
      (@comp_fapp0 C X B (@computational_cokernel_object C S A B m W)
        (@computational_cokernel_morphism C S A B m W) h)
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _ (@comp_assoc C Y X B (@computational_cokernel_object C S A B m W)
          (@computational_cokernel_morphism C S A B m W) h e))
        (@kernel_lift_postannihilation_path C S Y A B
          (@computational_cokernel_object C S A B m W) m
          (@hom_postcomp_factor_arrow C A B Y m (@comp_fapp0 C Y X B h e) covered)
          (@comp_fapp0 C Y X B h e)
          (@computational_cokernel_morphism C S A B m W)
          (@hom_postcomp_factor_path C A B Y m (@comp_fapp0 C Y X B h e) covered)
          (@computational_cokernel_annihilation C S A B m W))));

// Select the normal lift in the existing contractible Hom fibre.
symbol normal_mono_factor_from_epic_factor
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [Q : τ (@HasComputationalCokernels C S)]
  (M : τ (@HasLiftsAlongMonomorphisms C S Q))
  [A B X Y : τ (Obj C)]
  (m : τ (Hom C A B))
  (monic : τ (@IsMonic C A B m))
  (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (h : τ (Hom C X B))
  (covered : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  : τ (@HomPostcompFactor C A B X m h)
≔ is_contr_center (@normal_mono_lift_contr C S Q M A B m monic X
    (@normal_mono_test_from_epic_factor C S A B X Y m (Q A B m) e epic h covered));
