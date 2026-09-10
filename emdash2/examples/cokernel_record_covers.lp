/* The original quotient and test arrow survive canonical-cover reuse. */
require open emdash.emdash3_2_cokernel_record_covers;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@preabelian_preadditive C P t PA) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@preabelian_preadditive C P t PA) (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C (@preabelian_preadditive C P t PA) A B f)) ⊢
  @computational_chain_pair_d C (@preabelian_preadditive C P t PA) A B (@computational_cokernel_object C (@preabelian_preadditive C
    P t PA) A B f Q) (@cokernel_record_row_pair C (@preabelian_preadditive C P t PA) A B f Q) ≡ (@computational_cokernel_morphism C
    (@preabelian_preadditive C P t PA) A B f Q);

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@preabelian_preadditive C P t PA) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@preabelian_preadditive C P t PA) (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C (@preabelian_preadditive C P t PA) A B f)) (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C
    (@preabelian_preadditive C P t PA) B (@computational_cokernel_object C (@preabelian_preadditive C P t PA) A B f Q)
    (@computational_cokernel_morphism C (@preabelian_preadditive C P t PA) A B f Q) T)) ⊢
  @weak_kernel_annihilator_arrow C (@preabelian_preadditive C P t PA) B (@computational_cokernel_object C (@preabelian_preadditive C
    P t PA) A B f (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C (@preabelian_preadditive C P t PA) A B
    f (@preabelian_cokernel C P t PA A B f)) T
    (@cokernel_record_retarget_test C (@preabelian_preadditive C P t PA) A B f Q (@preabelian_cokernel C P t PA A B f) T test)
  ≡ @weak_kernel_annihilator_arrow C (@preabelian_preadditive C P t PA) B (@computational_cokernel_object C (@preabelian_preadditive
    C P t PA) A B f Q) (@computational_cokernel_morphism C (@preabelian_preadditive C P t PA) A B f Q) T test;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@preabelian_preadditive C P t PA) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@preabelian_preadditive C P t PA) (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C (@preabelian_preadditive C P t PA) A B f)) (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C
    (@preabelian_preadditive C P t PA) B (@computational_cokernel_object C (@preabelian_preadditive C P t PA) A B f Q)
    (@computational_cokernel_morphism C (@preabelian_preadditive C P t PA) A B f Q) T)) ⊢
  @abelian_cokernel_record_cover_explicit C P t PA M E A B f Q T test
  : τ (@ComputationalExactCoverWitness C P t PA A B (@computational_cokernel_object C (@preabelian_preadditive C P t PA) A B f Q)
    (@cokernel_record_row_pair C (@preabelian_preadditive C P t PA) A B f Q) T test);

assertnot [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@preabelian_preadditive C P t PA) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@preabelian_preadditive C P t PA) (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C (@preabelian_preadditive C P t PA) A B f)) ⊢
  @computational_cokernel_object C (@preabelian_preadditive C P t PA) A B f Q
  ≡ @computational_cokernel_object C (@preabelian_preadditive C P t PA) A B f (@preabelian_cokernel C P t PA A B f);
