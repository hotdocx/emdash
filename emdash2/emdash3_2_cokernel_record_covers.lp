/*
  Exact covers for a retained cokernel record.
  A universal colift changes only the annihilation proof of a test, not its
  arrow or the retained quotient. The canonical cover theorem then supplies
  the same cover-witness shape. The explicit point entry exposes the actual
  quotient as test owner, avoiding expensive projected-row reconstruction.
*/
require open emdash.emdash3_2_hom_factor_spaces;
require open emdash.emdash3_2_computational_homology;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;
require open emdash.emdash3_2_abelian_canonical_cokernel_covers;

// Only a universal colift is needed; no object equality or quotient replacement.
symbol cokernel_record_comparison_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q0 Q1 : τ (@ComputationalCokernel C S A B f))
  : τ (@HomPrecompFactor C B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_object C S A B f Q1)
    (@computational_cokernel_morphism C S A B f Q0) (@computational_cokernel_morphism C S A B f Q1))
≔ is_contr_center (@computational_cokernel_factor_contr C S A B f Q0 (@computational_cokernel_object C S A B f Q1) (@Struct_sigma
  (Hom C B (@computational_cokernel_object C S A B f Q1))
      (λ h : τ (Hom C B (@computational_cokernel_object C S A B f Q1)), @= (Hom C A (@computational_cokernel_object C S A B f Q1))
        (@comp_fapp0 C A B (@computational_cokernel_object C S A B f Q1) h f) (@preadditive_hom_zero C S A
          (@computational_cokernel_object C S A B f Q1)))
      (@computational_cokernel_morphism C S A B f Q1) (@computational_cokernel_annihilation C S A B f Q1)));

symbol cokernel_record_retarget_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q0 Q1 : τ (@ComputationalCokernel C S A B f)) (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C S B
    (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S A B f Q0) T))
  : τ (@= (Hom C T (@computational_cokernel_object C S A B f Q1))
      (@comp_fapp0 C T B (@computational_cokernel_object C S A B f Q1) (@computational_cokernel_morphism C S A B f Q1)
        (@weak_kernel_annihilator_arrow C S B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S A
        B f Q0) T test)) (@preadditive_hom_zero C S T (@computational_cokernel_object C S A B f Q1)))
≔ @eq_trans _ _ _ _
    (@eq_ap (Hom C B (@computational_cokernel_object C S A B f Q1)) (Hom C T (@computational_cokernel_object C S A B f Q1))
      (λ h : τ (Hom C B (@computational_cokernel_object C S A B f Q1)), @comp_fapp0 C T B (@computational_cokernel_object C S A B f
        Q1) h (@weak_kernel_annihilator_arrow C S B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism
        C S A B f Q0) T test)) _ _
      (@eq_sym _ _ _ (@hom_precomp_factor_path C B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_object C S
        A B f Q1) (@computational_cokernel_morphism C S A B f Q0) (@computational_cokernel_morphism C S A B f Q1)
        (@cokernel_record_comparison_factor C S A B f Q0 Q1))))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C T B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_object C S A B f Q1)
        (@hom_precomp_factor_arrow C B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_object C S A B f Q1)
        (@computational_cokernel_morphism C S A B f Q0) (@computational_cokernel_morphism C S A B f Q1)
        (@cokernel_record_comparison_factor C S A B f Q0 Q1)) (@computational_cokernel_morphism C S A B f Q0)
        (@weak_kernel_annihilator_arrow C S B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S A
        B f Q0) T test)))
      (@preadditive_postcompose_zero_path C S T (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_object C S A
        B f Q1) (@hom_precomp_factor_arrow C B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_object C S A B
        f Q1) (@computational_cokernel_morphism C S A B f Q0) (@computational_cokernel_morphism C S A B f Q1)
        (@cokernel_record_comparison_factor C S A B f Q0 Q1))
        (@comp_fapp0 C T B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S A B f Q0)
          (@weak_kernel_annihilator_arrow C S B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S
          A B f Q0) T test))
        (@weak_kernel_annihilator_path C S B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S A B
          f Q0) T test)));

symbol cokernel_record_retarget_test
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q0 Q1 : τ (@ComputationalCokernel C S A B f)) (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C S B
    (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S A B f Q0) T))
  : τ (@WeakKernelAnnihilator C S B (@computational_cokernel_object C S A B f Q1) (@computational_cokernel_morphism C S A B f Q1) T)
≔ @Struct_sigma (Hom C T B)
    (λ h : τ (Hom C T B), @= (Hom C T (@computational_cokernel_object C S A B f Q1))
      (@comp_fapp0 C T B (@computational_cokernel_object C S A B f Q1) (@computational_cokernel_morphism C S A B f Q1) h)
        (@preadditive_hom_zero C S T (@computational_cokernel_object C S A B f Q1)))
    (@weak_kernel_annihilator_arrow C S B (@computational_cokernel_object C S A B f Q0) (@computational_cokernel_morphism C S A B f
      Q0) T test) (@cokernel_record_retarget_zero C S A B f Q0 Q1 T test);

symbol cokernel_record_row_pair
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C S A B f))
  : τ (@ComputationalChainPair C S A B (@computational_cokernel_object C S A B f Q))
≔ @computational_chain_pair_intro C S A B (@computational_cokernel_object C S A B f Q)
    f (@computational_cokernel_morphism C S A B f Q)
    (@computational_cokernel_annihilation C S A B f Q);

symbol abelian_cokernel_record_covers_explicit
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@preabelian_preadditive C P t PA) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@preabelian_preadditive C P t PA) (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C (@preabelian_preadditive C P t PA) A B f))
  : τ (@HasComputationalExactCovers C P t PA A B (@computational_cokernel_object C (@preabelian_preadditive C P t PA) A B f Q)
    (@cokernel_record_row_pair C (@preabelian_preadditive C P t PA) A B f Q))
≔ λ T : τ (Obj C), λ test : τ (@WeakKernelAnnihilator C (@preabelian_preadditive C P t PA) B (@computational_cokernel_object C
  (@preabelian_preadditive C P t PA) A B f Q) (@computational_cokernel_morphism C (@preabelian_preadditive C P t PA) A B f Q) T),
    (@abelian_canonical_cokernel_covers_explicit C P t PA M E A B f)
      T (@cokernel_record_retarget_test C (@preabelian_preadditive C P t PA) A B f Q (@preabelian_cokernel C P t PA A B f) T test);

symbol abelian_cokernel_record_cover_explicit
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@computational_homology_preadditive C P t PA) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@computational_homology_preadditive C P t PA) (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)] (f : τ (Hom C A B))
  (Q : τ (@ComputationalCokernel C (@computational_homology_preadditive C P t PA) A B f))
  (T : τ (Obj C))
  (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t PA) B (@computational_cokernel_object C
    (@computational_homology_preadditive C P t PA) A B f Q) (@computational_cokernel_morphism C (@computational_homology_preadditive C P t PA) A B f Q) T))
  : τ (@ComputationalExactCoverWitness C P t PA A B (@computational_cokernel_object C (@computational_homology_preadditive C P t PA) A B f Q)
    (@cokernel_record_row_pair C (@computational_homology_preadditive C P t PA) A B f Q) T test)
≔ (@abelian_cokernel_record_covers_explicit C P t PA M E A B f Q) T test;
