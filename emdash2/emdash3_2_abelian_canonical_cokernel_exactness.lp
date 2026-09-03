/* Canonical cokernel exactness via an epic kernel-factor point. */

require open emdash.emdash3_2_abelian_canonical_cokernel_epic;

symbol abelian_canonical_cokernel_exact_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalExactAt C P t PA
      A B
      (@computational_cokernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_cokernel C P t PA A B f))
      (@abelian_canonical_cokernel_pair_explicit C P t PA A B f)
      (@abelian_canonical_cokernel_homology_explicit C P t PA A B f))
≔ @computational_exact_at_from_epic_factor_point C P t PA
    A B
    (@computational_cokernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@abelian_canonical_cokernel_pair_explicit C P t PA A B f)
    (@abelian_canonical_cokernel_homology_explicit C P t PA A B f)
    (@abelian_canonical_cokernel_candidate_point_explicit C P t PA A B f)
    (@abelian_canonical_cokernel_candidate_epic_explicit C P t
      PA M E A B f);
