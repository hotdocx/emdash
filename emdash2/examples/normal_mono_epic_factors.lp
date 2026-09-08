/* Local epic factors construct normal tests without a chosen section. */
require open emdash.emdash3_2_normal_mono_epic_factors;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B X Y : τ (Obj C))
  (m : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B m))
  (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (h : τ (Hom C X B))
  (covered : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  ⊢ @normal_mono_test_from_epic_factor C S A B X Y m W e epic h covered : τ (@NormalMonoTest C S A B m W X);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B X Y : τ (Obj C))
  (m : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B m))
  (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (h : τ (Hom C X B))
  (covered : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  ⊢ @weak_kernel_annihilator_arrow C S B
    (@computational_cokernel_object C S A B m W)
    (@computational_cokernel_morphism C S A B m W) X (@normal_mono_test_from_epic_factor C S A B X Y m W e epic h covered) ≡ h;

assertnot
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B X Y : τ (Obj C))
  (m : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B m))
  (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (h : τ (Hom C X B))
  (covered : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  (other : τ (Hom C X B))
  ⊢ @weak_kernel_annihilator_arrow C S B
    (@computational_cokernel_object C S A B m W)
    (@computational_cokernel_morphism C S A B m W) X (@normal_mono_test_from_epic_factor C S A B X Y m W e epic h covered) ≡ other;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (Q : τ (@HasComputationalCokernels C S))
  (M : τ (@HasLiftsAlongMonomorphisms C S Q))
  (A B X Y : τ (Obj C))
  (m : τ (Hom C A B))
  (monic : τ (@IsMonic C A B m))
  (e : τ (Hom C Y X))
  (epic : τ (@IsEpic C Y X e))
  (h : τ (Hom C X B))
  (covered : τ (@HomPostcompFactor C A B Y m (@comp_fapp0 C Y X B h e)))
  ⊢ @hom_postcomp_factor_path C A B X m h
      (@normal_mono_factor_from_epic_factor C S Q M A B X Y m monic e epic h covered)
  : τ (@= (Hom C X B)
      (@comp_fapp0 C X A B m
        (@hom_postcomp_factor_arrow C A B X m h
          (@normal_mono_factor_from_epic_factor C S Q M A B X Y m monic e epic h covered))) h);
