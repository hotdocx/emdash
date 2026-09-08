/* Use the already selected cycle factor, rather than rebuilding an all-test family. */
require open emdash.emdash3_2_hom_factor_comparison_pasting;
require open emdash.emdash3_2_normal_mono_epic_factors;

symbol normal_mono_test_from_cycle_point
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A K Q R : τ (Obj C)]
  (V : τ (@IsoEvidence C R Q))
  (c : τ (Hom C A Q)) (pi : τ (Hom C K R))
  (a : τ (Hom C A K))
  (forward : τ (@= (Hom C A R)
    (@comp_fapp0 C A Q R (@iso_evidence_from C R Q V) c)
    (@comp_fapp0 C A K R pi a)))
  [E T Z B H : τ (Obj C)]
  (e : τ (Hom C E T)) (epic : τ (@IsEpic C E T e))
  (delta : τ (Hom C T R))
  (mu : τ (Hom C K B)) (mu_monic : τ (@IsMonic C K B mu))
  (i : τ (Hom C A B))
  (comparison : τ (@= (Hom C A B) (@comp_fapp0 C A K B mu a) i))
  (h : τ (Hom C E B))
  (original : τ (@HomPostcompFactor C K B E mu h))
  (target : τ (@HomPostcompFactor C A B E i h))
  (k : τ (Hom C Z A))
  (cycles : τ (@HomPostcompFactor C Z A E k
    (@hom_postcomp_factor_arrow C A B E i h target)))
  (j : τ (Hom C H Q)) (W : τ (@ComputationalCokernel C S H Q j))
  (quotient : τ (@HomPostcompFactor C H Q Z j (@comp_fapp0 C Z A Q c k)))
  (cover : τ (@= (Hom C E R) (@comp_fapp0 C E T R delta e)
    (@comp_fapp0 C E K R pi (@hom_postcomp_factor_arrow C K B E mu h original))))
  : τ (@NormalMonoTest C S H Q j W T)
≔ @normal_mono_test_from_epic_factor C S H Q T E j W e epic
    (@comp_fapp0 C T R Q (@iso_evidence_to C R Q V) delta)
    (@homology_covered_factor_paste C E T K Z A H Q R
      e delta pi a k c j (@hom_postcomp_factor_arrow C K B E mu h original)
      (@iso_evidence_to C R Q V) (@iso_evidence_from C R Q V)
      (@monic_comparison_factor C A K B E i mu a comparison h original target mu_monic)
      cycles quotient cover forward (@iso_evidence_right C R Q V));
