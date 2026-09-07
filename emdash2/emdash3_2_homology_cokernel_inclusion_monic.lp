/*
  PA-explicit homology inclusion monicity.

  The constructor-visible Abelian value keeps normality projections immediate;
  the homology, cycle, and boundary owners still use the one literal PA.
*/
require open emdash.emdash3_2_homology_cokernel_inclusion;
require open emdash.emdash3_2_abelian_cokernel_composite_monic;

symbol homology_cokernel_inclusion_monic_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@computational_homology_preadditive C P t PA) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@computational_homology_preadditive C P t PA) (@preabelian_kernels C P t PA)))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (H : τ (@ComputationalHomologyAt C P t PA A B D pair))
  : τ
    (@IsMonic C
      (@computational_homology_object C P t PA A B D pair H)
      (@computational_cokernel_object C
        (@computational_homology_preadditive C P t PA) A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t PA) A B D pair)
        (@computational_homology_dnext_cokernel C P t PA A B D pair))
      (@computational_homology_cokernel_inclusion C P t PA A B D pair H))
≔ @abelian_cokernel_composite_comparison_monic C P t
    (@computational_abelian_category_intro C P t PA M E)
    A
      (@computational_homology_cycle_object C P t PA A B D pair H) B
      (@computational_homology_boundary C P t PA A B D pair H)
      (@computational_homology_cycle_embedding C P t PA A B D pair H)
      (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t PA) A B D pair)
      (@computational_homology_boundary_path C P t PA A B D pair H)
      (@computational_homology_cokernel C P t PA A B D pair H)
      (@computational_homology_dnext_cokernel C P t PA A B D pair)
    (@computational_kernel_morphism_is_monic C
        (@computational_homology_preadditive C P t PA) B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t PA) A B D pair)
        (@computational_homology_cycles C P t PA A B D pair H));
