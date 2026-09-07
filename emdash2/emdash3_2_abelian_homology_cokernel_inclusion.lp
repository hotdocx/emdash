/*
  One-Abelian-capability observation of the checked PA-explicit homology
  inclusion theorem. No endpoint transport or new equality is introduced.
*/
require open emdash.emdash3_2_homology_cokernel_inclusion_monic;

symbol abelian_homology_cokernel_inclusion_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ
      (@ComputationalChainPair C
        (@computational_homology_preadditive C P t
          (@abelian_stability_preabelian C P t Ab)) A B D))
  (H : τ (@ComputationalHomologyAt C P t (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ
    (@IsMonic C
      (@computational_homology_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_cokernel_object C
        (@computational_homology_preadditive C P t
          (@abelian_stability_preabelian C P t Ab)) A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t
            (@abelian_stability_preabelian C P t Ab)) A B D pair)
        (@computational_homology_dnext_cokernel C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair))
      (@computational_homology_cokernel_inclusion C P t (@abelian_stability_preabelian C P t Ab) A B D pair H))
≔ @homology_cokernel_inclusion_monic_explicit C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    A B D pair H;
