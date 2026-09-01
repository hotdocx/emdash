/* Reviewer-facing internal computational weak kernels. */

require open emdash.emdash3_2_weak_kernels;

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T : τ (Obj C))
  (alpha : τ (Hom C A B)) ⊢
  @WeakKernelAnnihilator C S A B alpha T
  : Grpd;

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T T' : τ (Obj C))
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T' T)) ⊢
  @weak_kernel_annihilator_reindex_func C S A B T' T alpha h
  : τ (@Functor
      (Path_cat (@WeakKernelAnnihilator C S A B alpha T))
      (Path_cat (@WeakKernelAnnihilator C S A B alpha T')));

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T T' : τ (Obj C))
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T' T))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T)) ⊢
  @fapp0
    (Path_cat (@WeakKernelAnnihilator C S A B alpha T))
    (Path_cat (@WeakKernelAnnihilator C S A B alpha T'))
    (@weak_kernel_annihilator_reindex_func C S A B T' T alpha h)
    cone
  ≡ @weak_kernel_annihilator_reindex_fapp0 C S A B T' T alpha h cone;

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T T' : τ (Obj C))
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T' T))
  (cone0 cone1 : τ (@WeakKernelAnnihilator C S A B alpha T)) ⊢
  @fapp1_func
    (Path_cat (@WeakKernelAnnihilator C S A B alpha T))
    (Path_cat (@WeakKernelAnnihilator C S A B alpha T'))
    (@weak_kernel_annihilator_reindex_func C S A B T' T alpha h)
    cone0 cone1
  : τ (@Functor
      (Hom_cat
        (Path_cat (@WeakKernelAnnihilator C S A B alpha T)) cone0 cone1)
      (Hom_cat
        (Path_cat (@WeakKernelAnnihilator C S A B alpha T'))
        (@weak_kernel_annihilator_reindex_fapp0
          C S A B T' T alpha h cone0)
        (@weak_kernel_annihilator_reindex_fapp0
          C S A B T' T alpha h cone1)));

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B K : τ (Obj C))
  (alpha : τ (Hom C A B))
  (kappa : τ (Hom C K A))
  (annihilation : τ (@= (Hom C K B)
    (@comp_fapp0 C K A B alpha kappa)
    (@preadditive_hom_zero C S K B)))
  (factor : τ (@WeakKernelFactorOperation C S A B alpha K))
  (law : τ (@WeakKernelFactorLaw C S A B alpha K kappa factor)) ⊢
  @computational_weak_kernel_intro C S A B alpha
    K kappa annihilation factor law
  : τ (@ComputationalWeakKernel C S A B alpha);

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B K : τ (Obj C))
  (alpha : τ (Hom C A B))
  (kappa : τ (Hom C K A))
  (annihilation : τ (@= (Hom C K B)
    (@comp_fapp0 C K A B alpha kappa)
    (@preadditive_hom_zero C S K B)))
  (factor : τ (@WeakKernelFactorOperation C S A B alpha K))
  (law : τ (@WeakKernelFactorLaw C S A B alpha K kappa factor)) ⊢
  @computational_weak_kernel_object C S A B alpha
    (@computational_weak_kernel_intro C S A B alpha
      K kappa annihilation factor law)
  ≡ K;

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B K T : τ (Obj C))
  (alpha : τ (Hom C A B))
  (kappa : τ (Hom C K A))
  (annihilation : τ (@= (Hom C K B)
    (@comp_fapp0 C K A B alpha kappa)
    (@preadditive_hom_zero C S K B)))
  (factor : τ (@WeakKernelFactorOperation C S A B alpha K))
  (law : τ (@WeakKernelFactorLaw C S A B alpha K kappa factor))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T)) ⊢
  @computational_weak_kernel_factor_path C S A B alpha
    (@computational_weak_kernel_intro C S A B alpha
      K kappa annihilation factor law)
    T cone
  : τ (@= (Hom C T A)
      (@comp_fapp0 C T K A kappa (factor T cone))
      (@weak_kernel_annihilator_arrow C S A B alpha T cone));

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B : τ (Obj C))
  (alpha : τ (Hom C A B))
  (W : τ (@ComputationalWeakKernel C S A B alpha)) ⊢
  @computational_weak_kernel_is_weak C S A B alpha W
  : τ (@WeakKernel C S A B alpha);

assert (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (W : τ (@HasComputationalWeakKernels C S)) ⊢
  @computational_weak_kernels_are_weak C S W
  : τ (@HasWeakKernels C S);

assertnot (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B T T' : τ (Obj C))
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T' T)) ⊢
  @weak_kernel_annihilator_reindex_func C S A B T' T alpha h
  : τ (@Functor
      (Path_cat (@WeakKernelAnnihilator C S A B alpha T'))
      (Path_cat (@WeakKernelAnnihilator C S A B alpha T)));
