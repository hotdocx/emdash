/* Reviewer-facing consumers for genuine computational kernels/cokernels. */

require open emdash.emdash3_2_kernels_cokernels;

// Cokernel test objects retain covariant whole Path action.
assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T T' : τ (Obj C))
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T T'))
  ⊢ @cokernel_coannihilator_reindex_func C S A B T T' alpha h
  : τ (Functor
      (Path_cat (@CokernelCoannihilator C S A B alpha T))
      (Path_cat (@CokernelCoannihilator C S A B alpha T')));

// The selected centre of a contractible kernel factor space is a real lift.
assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalKernel C S A B alpha))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  ⊢ @computational_kernel_lift C S A B alpha W T cone
  : τ (Hom C T (@computational_kernel_object C S A B alpha W));

// Its fibre path is the kernel reconstruction equation.
assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalKernel C S A B alpha))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  ⊢ @computational_kernel_lift_path C S A B alpha W T cone
  : τ (@= (Hom C T A)
      (@comp_fapp0 C T
        (@computational_kernel_object C S A B alpha W) A
        (@computational_kernel_morphism C S A B alpha W)
        (@computational_kernel_lift C S A B alpha W T cone))
      (@weak_kernel_annihilator_arrow C S A B alpha T cone));

// Contraction gives uniqueness of every competing kernel factor.
assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalKernel C S A B alpha))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  (u : τ (Hom C T (@computational_kernel_object C S A B alpha W)))
  (p : τ (@= (Hom C T A)
    (@comp_fapp0 C T
      (@computational_kernel_object C S A B alpha W) A
      (@computational_kernel_morphism C S A B alpha W) u)
    (@weak_kernel_annihilator_arrow C S A B alpha T cone)))
  ⊢ @computational_kernel_lift_unique_path
      C S A B alpha W T cone u p
  : τ (@= (Hom C T (@computational_kernel_object C S A B alpha W))
      (@computational_kernel_lift C S A B alpha W T cone) u);

// Cokernel colifts expose the dual reconstruction and uniqueness laws.
assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B alpha))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  ⊢ @computational_cokernel_colift_path C S A B alpha W T cone
  : τ (@= (Hom C B T)
      (@comp_fapp0 C B
        (@computational_cokernel_object C S A B alpha W) T
        (@computational_cokernel_colift C S A B alpha W T cone)
        (@computational_cokernel_morphism C S A B alpha W))
      (@cokernel_coannihilator_arrow C S A B alpha T cone));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B alpha))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  (u : τ (Hom C (@computational_cokernel_object C S A B alpha W) T))
  (p : τ (@= (Hom C B T)
    (@comp_fapp0 C B
      (@computational_cokernel_object C S A B alpha W) T
      u (@computational_cokernel_morphism C S A B alpha W))
    (@cokernel_coannihilator_arrow C S A B alpha T cone)))
  ⊢ @computational_cokernel_colift_unique_path
      C S A B alpha W T cone u p
  : τ (@= (Hom C (@computational_cokernel_object C S A B alpha W) T)
      (@computational_cokernel_colift C S A B alpha W T cone) u);

// A selected pre-Abelian package retains its exact additive owner.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@PreAbelianCategory C P t))
  ⊢ @preabelian_additive C P t A
  : τ (@AdditiveCategory C P t);
