/* Reviewer-facing generic normality and computational Abelian consumers. */

require open emdash.emdash3_2_abelian_categories;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalKernel C S A B alpha))
  ⊢ @computational_kernel_morphism_is_monic C S A B alpha W
  : τ (@IsMonic C
      (@computational_kernel_object C S A B alpha W) A
      (@computational_kernel_morphism C S A B alpha W));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B alpha))
  ⊢ @computational_cokernel_morphism_is_epic C S A B alpha W
  : τ (@IsEpic C B
      (@computational_cokernel_object C S A B alpha W)
      (@computational_cokernel_morphism C S A B alpha W));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (Q : τ (@HasComputationalCokernels C S))
  (N : τ (@HasLiftsAlongMonomorphisms C S Q))
  (A B T : τ (Obj C))
  (m : τ (Hom C A B))
  (monic : τ (@IsMonic C A B m))
  (test : τ (@NormalMonoTest C S A B m (Q A B m) T))
  ⊢ @lift_along_monomorphism C S Q N A B m monic T test
  : τ (Hom C T A);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (Q : τ (@HasComputationalCokernels C S))
  (N : τ (@HasLiftsAlongMonomorphisms C S Q))
  (A B T : τ (Obj C))
  (m : τ (Hom C A B))
  (monic : τ (@IsMonic C A B m))
  (test : τ (@NormalMonoTest C S A B m (Q A B m) T))
  ⊢ @lift_along_monomorphism_path C S Q N A B m monic T test
  : τ (@= (Hom C T B)
      (@comp_fapp0 C T A B m
        (@lift_along_monomorphism C S Q N A B m monic T test))
      (@weak_kernel_annihilator_arrow C S B
        (@computational_cokernel_object C S A B m (Q A B m))
        (@computational_cokernel_morphism C S A B m (Q A B m)) T test));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (Q : τ (@HasComputationalCokernels C S))
  (N : τ (@HasLiftsAlongMonomorphisms C S Q))
  (A B T : τ (Obj C))
  (m : τ (Hom C A B))
  (monic : τ (@IsMonic C A B m))
  (test : τ (@NormalMonoTest C S A B m (Q A B m) T))
  (u : τ (Hom C T A))
  (p : τ (@= (Hom C T B)
    (@comp_fapp0 C T A B m u)
    (@weak_kernel_annihilator_arrow C S B
      (@computational_cokernel_object C S A B m (Q A B m))
      (@computational_cokernel_morphism C S A B m (Q A B m)) T test)))
  ⊢ @lift_along_monomorphism_unique_path
      C S Q N A B m monic T test u p
  : τ (@= (Hom C T A)
      (@lift_along_monomorphism C S Q N A B m monic T test) u);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (K : τ (@HasComputationalKernels C S))
  (N : τ (@HasColiftsAlongEpimorphisms C S K))
  (A B T : τ (Obj C))
  (e : τ (Hom C A B))
  (epic : τ (@IsEpic C A B e))
  (test : τ (@NormalEpiTest C S A B e (K A B e) T))
  ⊢ @colift_along_epimorphism C S K N A B e epic T test
  : τ (Hom C B T);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (K : τ (@HasComputationalKernels C S))
  (N : τ (@HasColiftsAlongEpimorphisms C S K))
  (A B T : τ (Obj C))
  (e : τ (Hom C A B))
  (epic : τ (@IsEpic C A B e))
  (test : τ (@NormalEpiTest C S A B e (K A B e) T))
  ⊢ @colift_along_epimorphism_path C S K N A B e epic T test
  : τ (@= (Hom C A T)
      (@comp_fapp0 C A B T
        (@colift_along_epimorphism C S K N A B e epic T test) e)
      (@cokernel_coannihilator_arrow C S
        (@computational_kernel_object C S A B e (K A B e)) A
        (@computational_kernel_morphism C S A B e (K A B e)) T test));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (K : τ (@HasComputationalKernels C S))
  (N : τ (@HasColiftsAlongEpimorphisms C S K))
  (A B T : τ (Obj C))
  (e : τ (Hom C A B))
  (epic : τ (@IsEpic C A B e))
  (test : τ (@NormalEpiTest C S A B e (K A B e) T))
  (u : τ (Hom C B T))
  (p : τ (@= (Hom C A T)
    (@comp_fapp0 C A B T u e)
    (@cokernel_coannihilator_arrow C S
      (@computational_kernel_object C S A B e (K A B e)) A
      (@computational_kernel_morphism C S A B e (K A B e)) T test)))
  ⊢ @colift_along_epimorphism_unique_path
      C S K N A B e epic T test u p
  : τ (@= (Hom C B T)
      (@colift_along_epimorphism C S K N A B e epic T test) u);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@ComputationalAbelianCategory C P t))
  ⊢ @computational_abelian_preabelian C P t A
  : τ (@PreAbelianCategory C P t);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@ComputationalAbelianCategory C P t))
  ⊢ @computational_abelian_mono_lifts C P t A
  : τ (@HasLiftsAlongMonomorphisms C
      (@additive_preadditive C P t
        (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t A)))
      (@preabelian_cokernels C P t
        (@computational_abelian_preabelian C P t A)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@ComputationalAbelianCategory C P t))
  ⊢ @computational_abelian_epi_colifts C P t A
  : τ (@HasColiftsAlongEpimorphisms C
      (@additive_preadditive C P t
        (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t A)))
      (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t A)));
