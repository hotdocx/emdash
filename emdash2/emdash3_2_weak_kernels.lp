/*
  Internal computational weak kernels in a preadditive category.

  Annihilated maps are the homotopy fibre of ordinary postcomposition at the
  selected zero arrow. Test-object reindexing is a transparent Path-map
  functor, retaining arbitrary equality/higher action without postulating a
  separate cone-square grammar. A computational weak kernel selects an object,
  arrow, annihilation path, nonunique factor operation, and reconstruction
  law. No kernel, monicity, uniqueness, or Abelian structure is claimed.
*/

require open emdash.emdash3_2_additive_categories;
require open emdash.emdash3_2_truncation_reflector;

// Ordinary postcomposition by alpha, retained as a whole Hom functor.
symbol weak_kernel_postcomp_func
  [C : Cat]
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (T : τ (Obj C))
  : τ (Functor (Hom_cat C T A) (Hom_cat C T B))
≔ @hom_postcomp_func C C (@id_func C) T A B alpha;

// Typed proof-time reading of its point action as ordinary composition.
symbol weak_kernel_postcomp_fapp0_path
  [C : Cat]
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (T : τ (Obj C))
  (tau : τ (Hom C T A))
  : τ (@= (Hom C T B)
      (@fapp0
        (Hom_cat C T A) (Hom_cat C T B)
        (@weak_kernel_postcomp_func C A B alpha T) tau)
      (@comp_fapp0 C T A B alpha tau))
≔ @eq_refl _
    (@fapp0
      (Hom_cat C T A) (Hom_cat C T B)
      (@weak_kernel_postcomp_func C A B alpha T) tau);

// Ann_alpha(T) = { tau : T -> A | alpha o tau = 0 }.
symbol WeakKernelAnnihilator
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (T : τ (Obj C))
  : Grpd
≔ @HFiber
    (Hom C T A)
    (Hom C T B)
    (λ tau : τ (Hom C T A),
      @comp_fapp0 C T A B alpha tau)
    (@preadditive_hom_zero C S T B);

// Readable arrow and annihilation projections of one test cone.
symbol weak_kernel_annihilator_arrow
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (Hom C T A)
≔ @hfiber_point
    (Hom C T A) (Hom C T B)
    (λ tau : τ (Hom C T A), @comp_fapp0 C T A B alpha tau)
    (@preadditive_hom_zero C S T B)
    cone;

symbol weak_kernel_annihilator_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (@= (Hom C T B)
      (@comp_fapp0 C T A B alpha
        (@weak_kernel_annihilator_arrow C S A B alpha T cone))
      (@preadditive_hom_zero C S T B))
≔ @hfiber_path
    (Hom C T A) (Hom C T B)
    (λ tau : τ (Hom C T A), @comp_fapp0 C T A B alpha tau)
    (@preadditive_hom_zero C S T B)
    cone;

// Reindex an annihilated map along h : T' -> T.
symbol weak_kernel_annihilator_reindex_fapp0
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T' T : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T' T))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (@WeakKernelAnnihilator C S A B alpha T')
≔ @Struct_sigma
    (Hom C T' A)
    (λ tau : τ (Hom C T' A),
      @= (Hom C T' B)
        (@comp_fapp0 C T' A B alpha tau)
        (@preadditive_hom_zero C S T' B))
    (@comp_fapp0 C T' T A
      (@weak_kernel_annihilator_arrow C S A B alpha T cone) h)
    (@eq_trans
      (Hom C T' B)
      (@comp_fapp0 C T' A B alpha
        (@comp_fapp0 C T' T A
          (@weak_kernel_annihilator_arrow C S A B alpha T cone) h))
      (@comp_fapp0 C T' T B
        (@comp_fapp0 C T A B alpha
          (@weak_kernel_annihilator_arrow C S A B alpha T cone)) h)
      (@preadditive_hom_zero C S T' B)
      (@comp_assoc C T' T A B alpha
        (@weak_kernel_annihilator_arrow C S A B alpha T cone) h)
      (@eq_trans
        (Hom C T' B)
        (@comp_fapp0 C T' T B
          (@comp_fapp0 C T A B alpha
            (@weak_kernel_annihilator_arrow C S A B alpha T cone)) h)
        (@comp_fapp0 C T' T B
          (@preadditive_hom_zero C S T B) h)
        (@preadditive_hom_zero C S T' B)
        (@eq_ap
          (Hom C T B) (Hom C T' B)
          (λ q : τ (Hom C T B), @comp_fapp0 C T' T B q h)
          (@comp_fapp0 C T A B alpha
            (@weak_kernel_annihilator_arrow C S A B alpha T cone))
          (@preadditive_hom_zero C S T B)
          (@weak_kernel_annihilator_path C S A B alpha T cone))
        (@preadditive_comp_zero_left_path C S T' T B h)));

// Whole Path action of reindexing; every higher equality action remains.
symbol weak_kernel_annihilator_reindex_func
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T' T : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T' T))
  : τ (Functor
      (Path_cat (@WeakKernelAnnihilator C S A B alpha T))
      (Path_cat (@WeakKernelAnnihilator C S A B alpha T')))
≔ @path_map_func
    (@WeakKernelAnnihilator C S A B alpha T)
    (@WeakKernelAnnihilator C S A B alpha T')
    (λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
      @weak_kernel_annihilator_reindex_fapp0 C S A B T' T alpha h cone);

// Selected factor operation for a fixed candidate object K.
symbol WeakKernelFactorOperation
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (K : τ (Obj C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ T : τ (Obj C),
    @Function_grpd
      (@WeakKernelAnnihilator C S A B alpha T)
      (Hom C T K));

// Reconstruction law kappa o factor(tau,p) = tau; no uniqueness is stored.
symbol WeakKernelFactorLaw
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  [K : τ (Obj C)]
  (kappa : τ (Hom C K A))
  (factor : τ (@WeakKernelFactorOperation C S A B alpha K))
  : Grpd
≔ @Pi_grpd (Obj C) (λ T : τ (Obj C),
    @Pi_grpd (@WeakKernelAnnihilator C S A B alpha T)
      (λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
        @= (Hom C T A)
          (@comp_fapp0 C T K A kappa (factor T cone))
          (@weak_kernel_annihilator_arrow C S A B alpha T cone)));

// Object, arrow, annihilation, factor operation, and reconstruction law.
symbol ComputationalWeakKernel
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  : Grpd
≔ `Σ_ K : τ (Obj C),
   `Σ_ kappa : τ (Hom C K A),
   `Σ_ annihilation : τ (@= (Hom C K B)
      (@comp_fapp0 C K A B alpha kappa)
      (@preadditive_hom_zero C S K B)),
   `Σ_ factor : τ (@WeakKernelFactorOperation C S A B alpha K),
       @WeakKernelFactorLaw C S A B alpha K kappa factor;

symbol computational_weak_kernel_intro
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (K : τ (Obj C))
  (kappa : τ (Hom C K A))
  (annihilation : τ (@= (Hom C K B)
    (@comp_fapp0 C K A B alpha kappa)
    (@preadditive_hom_zero C S K B)))
  (factor : τ (@WeakKernelFactorOperation C S A B alpha K))
  (law : τ (@WeakKernelFactorLaw C S A B alpha K kappa factor))
  : τ (@ComputationalWeakKernel C S A B alpha)
≔ @Struct_sigma
    (Obj C)
    (λ K0 : τ (Obj C),
      `Σ_ kappa0 : τ (Hom C K0 A),
      `Σ_ annihilation0 : τ (@= (Hom C K0 B)
        (@comp_fapp0 C K0 A B alpha kappa0)
        (@preadditive_hom_zero C S K0 B)),
      `Σ_ factor0 : τ (@WeakKernelFactorOperation C S A B alpha K0),
        @WeakKernelFactorLaw C S A B alpha K0 kappa0 factor0)
    K
    (@Struct_sigma
      (Hom C K A)
      (λ kappa0 : τ (Hom C K A),
        `Σ_ annihilation0 : τ (@= (Hom C K B)
          (@comp_fapp0 C K A B alpha kappa0)
          (@preadditive_hom_zero C S K B)),
        `Σ_ factor0 : τ (@WeakKernelFactorOperation C S A B alpha K),
          @WeakKernelFactorLaw C S A B alpha K kappa0 factor0)
      kappa
      (@Struct_sigma
        (@= (Hom C K B)
          (@comp_fapp0 C K A B alpha kappa)
          (@preadditive_hom_zero C S K B))
        (λ _ : τ (@= (Hom C K B)
          (@comp_fapp0 C K A B alpha kappa)
          (@preadditive_hom_zero C S K B)),
          `Σ_ factor0 : τ (@WeakKernelFactorOperation C S A B alpha K),
            @WeakKernelFactorLaw C S A B alpha K kappa factor0)
        annihilation
        (@Struct_sigma
          (@WeakKernelFactorOperation C S A B alpha K)
          (λ factor0 : τ (@WeakKernelFactorOperation C S A B alpha K),
            @WeakKernelFactorLaw C S A B alpha K kappa factor0)
          factor law)));

// Readable projections.
symbol computational_weak_kernel_object
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalWeakKernel C S A B alpha))
  : τ (Obj C)
≔ sigma_Fst W;

symbol computational_weak_kernel_morphism
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalWeakKernel C S A B alpha))
  : τ (Hom C (@computational_weak_kernel_object C S A B alpha W) A)
≔ sigma_Fst (sigma_Snd W);

symbol computational_weak_kernel_annihilation
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalWeakKernel C S A B alpha))
  : τ (@= (Hom C (@computational_weak_kernel_object C S A B alpha W) B)
      (@comp_fapp0 C
        (@computational_weak_kernel_object C S A B alpha W) A B
        alpha (@computational_weak_kernel_morphism C S A B alpha W))
      (@preadditive_hom_zero C S
        (@computational_weak_kernel_object C S A B alpha W) B))
≔ sigma_Fst (sigma_Snd (sigma_Snd W));

symbol computational_weak_kernel_factor_operation
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalWeakKernel C S A B alpha))
  : τ (@WeakKernelFactorOperation C S A B alpha
      (@computational_weak_kernel_object C S A B alpha W))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd W)));

symbol computational_weak_kernel_factor_fapp0
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalWeakKernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (Hom C T (@computational_weak_kernel_object C S A B alpha W))
≔ (@computational_weak_kernel_factor_operation C S A B alpha W) T cone;

symbol computational_weak_kernel_factor_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalWeakKernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (@= (Hom C T A)
      (@comp_fapp0 C T
        (@computational_weak_kernel_object C S A B alpha W) A
        (@computational_weak_kernel_morphism C S A B alpha W)
        (@computational_weak_kernel_factor_fapp0 C S A B alpha W T cone))
      (@weak_kernel_annihilator_arrow C S A B alpha T cone))
≔ (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd W)))) T cone;

// Proposition-valued ordinary existence, derived from computational data.
symbol WeakKernel
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  : Grpd
≔ @Trunc_grpd trunc_minus_one (@ComputationalWeakKernel C S A B alpha);

symbol computational_weak_kernel_is_weak
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalWeakKernel C S A B alpha))
  : τ (@WeakKernel C S A B alpha)
≔ @trunc_intro trunc_minus_one (@ComputationalWeakKernel C S A B alpha) W;

// Whole capability on every arrow of one preadditive category.
symbol HasComputationalWeakKernels
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ alpha : τ (Hom C A B),
        @ComputationalWeakKernel C S A B alpha)));

symbol HasWeakKernels
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ alpha : τ (Hom C A B),
        @WeakKernel C S A B alpha)));

symbol computational_weak_kernels_are_weak
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalWeakKernels C S))
  : τ (@HasWeakKernels C S)
≔ λ A : τ (Obj C), λ B : τ (Obj C), λ alpha : τ (Hom C A B),
    @computational_weak_kernel_is_weak C S A B alpha (W A B alpha);
