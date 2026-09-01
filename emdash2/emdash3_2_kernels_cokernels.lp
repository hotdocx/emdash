/*
  Genuine computational kernels and cokernels in a preadditive category.

  Annihilated and coannihilated maps are internal Hom fibres. For every test
  map, a genuine universal construction requires its factor space to be
  contractible: the centre is the selected lift/colift, the fibre path is
  reconstruction, and contraction supplies uniqueness. Weak-kernel factors
  remain separately nonunique. No manual cone-square grammar is introduced.
*/

require open emdash.emdash3_2_weak_kernels;

// Coann_alpha(T) = { tau : B -> T | tau o alpha = 0 }.
symbol CokernelCoannihilator
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (T : τ (Obj C))
  : Grpd
≔ @HFiber
    (Hom C B T)
    (Hom C A T)
    (λ tau : τ (Hom C B T),
      @comp_fapp0 C A B T tau alpha)
    (@preadditive_hom_zero C S A T);

symbol cokernel_coannihilator_arrow
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  [T : τ (Obj C)]
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  : τ (Hom C B T)
≔ @hfiber_point
    (Hom C B T) (Hom C A T)
    (λ tau : τ (Hom C B T), @comp_fapp0 C A B T tau alpha)
    (@preadditive_hom_zero C S A T)
    cone;

symbol cokernel_coannihilator_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  [T : τ (Obj C)]
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  : τ (@= (Hom C A T)
      (@comp_fapp0 C A B T
        (@cokernel_coannihilator_arrow C S A B alpha T cone) alpha)
      (@preadditive_hom_zero C S A T))
≔ @hfiber_path
    (Hom C B T) (Hom C A T)
    (λ tau : τ (Hom C B T), @comp_fapp0 C A B T tau alpha)
    (@preadditive_hom_zero C S A T)
    cone;

// Covariantly reindex a coannihilated arrow along h : T -> T'.
symbol cokernel_coannihilator_reindex_fapp0
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T T' : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T T'))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  : τ (@CokernelCoannihilator C S A B alpha T')
≔ @Struct_sigma
    (Hom C B T')
    (λ tau : τ (Hom C B T'),
      @= (Hom C A T')
        (@comp_fapp0 C A B T' tau alpha)
        (@preadditive_hom_zero C S A T'))
    (@comp_fapp0 C B T T' h
      (@cokernel_coannihilator_arrow C S A B alpha T cone))
    (@eq_trans
      (Hom C A T')
      (@comp_fapp0 C A B T'
        (@comp_fapp0 C B T T' h
          (@cokernel_coannihilator_arrow C S A B alpha T cone))
        alpha)
      (@comp_fapp0 C A T T' h
        (@comp_fapp0 C A B T
          (@cokernel_coannihilator_arrow C S A B alpha T cone) alpha))
      (@preadditive_hom_zero C S A T')
      (@eq_sym
        (Hom C A T')
        (@comp_fapp0 C A T T' h
          (@comp_fapp0 C A B T
            (@cokernel_coannihilator_arrow C S A B alpha T cone) alpha))
        (@comp_fapp0 C A B T'
          (@comp_fapp0 C B T T' h
            (@cokernel_coannihilator_arrow C S A B alpha T cone))
          alpha)
        (@comp_assoc C A B T T' h
          (@cokernel_coannihilator_arrow C S A B alpha T cone) alpha))
      (@eq_trans
        (Hom C A T')
        (@comp_fapp0 C A T T' h
          (@comp_fapp0 C A B T
            (@cokernel_coannihilator_arrow C S A B alpha T cone) alpha))
        (@comp_fapp0 C A T T' h
          (@preadditive_hom_zero C S A T))
        (@preadditive_hom_zero C S A T')
        (@eq_ap
          (Hom C A T) (Hom C A T')
          (λ q : τ (Hom C A T), @comp_fapp0 C A T T' h q)
          (@comp_fapp0 C A B T
            (@cokernel_coannihilator_arrow C S A B alpha T cone) alpha)
          (@preadditive_hom_zero C S A T)
          (@cokernel_coannihilator_path C S A B alpha T cone))
        (@preadditive_comp_zero_right_path C S A T T' h)));

symbol cokernel_coannihilator_reindex_func
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B T T' : τ (Obj C)]
  (alpha : τ (Hom C A B))
  (h : τ (Hom C T T'))
  : τ (Functor
      (Path_cat (@CokernelCoannihilator C S A B alpha T))
      (Path_cat (@CokernelCoannihilator C S A B alpha T')))
≔ @path_map_func
    (@CokernelCoannihilator C S A B alpha T)
    (@CokernelCoannihilator C S A B alpha T')
    (λ cone : τ (@CokernelCoannihilator C S A B alpha T),
      @cokernel_coannihilator_reindex_fapp0 C S A B T T' alpha h cone);

// Factors u : T -> K satisfying kappa o u = arrow(cone).
symbol KernelFactorSpace
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  [K : τ (Obj C)]
  (kappa : τ (Hom C K A))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : Grpd
≔ @HFiber
    (Hom C T K)
    (Hom C T A)
    (λ u : τ (Hom C T K), @comp_fapp0 C T K A kappa u)
    (@weak_kernel_annihilator_arrow C S A B alpha T cone);

// Colifts u : Q -> T satisfying u o q = arrow(cone).
symbol CokernelFactorSpace
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  [Q : τ (Obj C)]
  (q : τ (Hom C B Q))
  (T : τ (Obj C))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  : Grpd
≔ @HFiber
    (Hom C Q T)
    (Hom C B T)
    (λ u : τ (Hom C Q T), @comp_fapp0 C B Q T u q)
    (@cokernel_coannihilator_arrow C S A B alpha T cone);

// Selected genuine kernel: every factor space is contractible.
symbol ComputationalKernel
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
   @Pi_grpd (Obj C) (λ T : τ (Obj C),
     @Pi_grpd (@WeakKernelAnnihilator C S A B alpha T)
       (λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
         IsContr (@KernelFactorSpace C S A B alpha K kappa T cone)));

symbol computational_kernel_intro
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (K : τ (Obj C))
  (kappa : τ (Hom C K A))
  (annihilation : τ (@= (Hom C K B)
    (@comp_fapp0 C K A B alpha kappa)
    (@preadditive_hom_zero C S K B)))
  (universal : τ (@Pi_grpd (Obj C) (λ T : τ (Obj C),
    @Pi_grpd (@WeakKernelAnnihilator C S A B alpha T)
      (λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
        IsContr (@KernelFactorSpace C S A B alpha K kappa T cone)))))
  : τ (@ComputationalKernel C S A B alpha)
≔ @Struct_sigma
    (Obj C)
    (λ K0 : τ (Obj C),
      `Σ_ kappa0 : τ (Hom C K0 A),
      `Σ_ annihilation0 : τ (@= (Hom C K0 B)
        (@comp_fapp0 C K0 A B alpha kappa0)
        (@preadditive_hom_zero C S K0 B)),
      @Pi_grpd (Obj C) (λ T : τ (Obj C),
        @Pi_grpd (@WeakKernelAnnihilator C S A B alpha T)
          (λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
            IsContr (@KernelFactorSpace C S A B alpha K0 kappa0 T cone))))
    K
    (@Struct_sigma
      (Hom C K A)
      (λ kappa0 : τ (Hom C K A),
        `Σ_ annihilation0 : τ (@= (Hom C K B)
          (@comp_fapp0 C K A B alpha kappa0)
          (@preadditive_hom_zero C S K B)),
        @Pi_grpd (Obj C) (λ T : τ (Obj C),
          @Pi_grpd (@WeakKernelAnnihilator C S A B alpha T)
            (λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
              IsContr (@KernelFactorSpace C S A B alpha K kappa0 T cone))))
      kappa
      (@Struct_sigma
        (@= (Hom C K B)
          (@comp_fapp0 C K A B alpha kappa)
          (@preadditive_hom_zero C S K B))
        (λ _ : τ (@= (Hom C K B)
          (@comp_fapp0 C K A B alpha kappa)
          (@preadditive_hom_zero C S K B)),
          @Pi_grpd (Obj C) (λ T : τ (Obj C),
            @Pi_grpd (@WeakKernelAnnihilator C S A B alpha T)
              (λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
                IsContr (@KernelFactorSpace C S A B alpha K kappa T cone))))
        annihilation universal));

symbol computational_kernel_object
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  : τ (Obj C)
≔ sigma_Fst W;

symbol computational_kernel_morphism
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  : τ (Hom C (@computational_kernel_object C S A B alpha W) A)
≔ sigma_Fst (sigma_Snd W);

symbol computational_kernel_annihilation
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  : τ (@= (Hom C (@computational_kernel_object C S A B alpha W) B)
      (@comp_fapp0 C
        (@computational_kernel_object C S A B alpha W) A B
        alpha (@computational_kernel_morphism C S A B alpha W))
      (@preadditive_hom_zero C S
        (@computational_kernel_object C S A B alpha W) B))
≔ sigma_Fst (sigma_Snd (sigma_Snd W));

symbol computational_kernel_factor_contr
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (IsContr (@KernelFactorSpace C S A B alpha
      (@computational_kernel_object C S A B alpha W)
      (@computational_kernel_morphism C S A B alpha W) T cone))
≔ (sigma_Snd (sigma_Snd (sigma_Snd W))) T cone;

symbol computational_kernel_lift
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (Hom C T (@computational_kernel_object C S A B alpha W))
≔ @hfiber_point
    (Hom C T (@computational_kernel_object C S A B alpha W))
    (Hom C T A)
    (λ u : τ (Hom C T (@computational_kernel_object C S A B alpha W)),
      @comp_fapp0 C T
        (@computational_kernel_object C S A B alpha W) A
        (@computational_kernel_morphism C S A B alpha W) u)
    (@weak_kernel_annihilator_arrow C S A B alpha T cone)
    (is_contr_center
      (@computational_kernel_factor_contr C S A B alpha W T cone));

symbol computational_kernel_lift_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  : τ (@= (Hom C T A)
      (@comp_fapp0 C T
        (@computational_kernel_object C S A B alpha W) A
        (@computational_kernel_morphism C S A B alpha W)
        (@computational_kernel_lift C S A B alpha W T cone))
      (@weak_kernel_annihilator_arrow C S A B alpha T cone))
≔ @hfiber_path
    (Hom C T (@computational_kernel_object C S A B alpha W))
    (Hom C T A)
    (λ u : τ (Hom C T (@computational_kernel_object C S A B alpha W)),
      @comp_fapp0 C T
        (@computational_kernel_object C S A B alpha W) A
        (@computational_kernel_morphism C S A B alpha W) u)
    (@weak_kernel_annihilator_arrow C S A B alpha T cone)
    (is_contr_center
      (@computational_kernel_factor_contr C S A B alpha W T cone));

symbol computational_kernel_lift_unique_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C S A B alpha T))
  (u : τ (Hom C T (@computational_kernel_object C S A B alpha W)))
  (p : τ (@= (Hom C T A)
    (@comp_fapp0 C T
      (@computational_kernel_object C S A B alpha W) A
      (@computational_kernel_morphism C S A B alpha W) u)
    (@weak_kernel_annihilator_arrow C S A B alpha T cone)))
  : τ (@= (Hom C T (@computational_kernel_object C S A B alpha W))
      (@computational_kernel_lift C S A B alpha W T cone) u)
≔ @eq_ap
    (@KernelFactorSpace C S A B alpha
      (@computational_kernel_object C S A B alpha W)
      (@computational_kernel_morphism C S A B alpha W) T cone)
    (Hom C T (@computational_kernel_object C S A B alpha W))
    (λ factor : τ (@KernelFactorSpace C S A B alpha
      (@computational_kernel_object C S A B alpha W)
      (@computational_kernel_morphism C S A B alpha W) T cone),
      @hfiber_point
        (Hom C T (@computational_kernel_object C S A B alpha W))
        (Hom C T A)
        (λ v : τ (Hom C T (@computational_kernel_object C S A B alpha W)),
          @comp_fapp0 C T
            (@computational_kernel_object C S A B alpha W) A
            (@computational_kernel_morphism C S A B alpha W) v)
        (@weak_kernel_annihilator_arrow C S A B alpha T cone)
        factor)
    (is_contr_center
      (@computational_kernel_factor_contr C S A B alpha W T cone))
    (@Struct_sigma
      (Hom C T (@computational_kernel_object C S A B alpha W))
      (λ v : τ (Hom C T (@computational_kernel_object C S A B alpha W)),
        @= (Hom C T A)
          (@comp_fapp0 C T
            (@computational_kernel_object C S A B alpha W) A
            (@computational_kernel_morphism C S A B alpha W) v)
          (@weak_kernel_annihilator_arrow C S A B alpha T cone))
      u p)
    (is_contr_path
      (@computational_kernel_factor_contr C S A B alpha W T cone)
      (@Struct_sigma
        (Hom C T (@computational_kernel_object C S A B alpha W))
        (λ v : τ (Hom C T (@computational_kernel_object C S A B alpha W)),
          @= (Hom C T A)
            (@comp_fapp0 C T
              (@computational_kernel_object C S A B alpha W) A
              (@computational_kernel_morphism C S A B alpha W) v)
            (@weak_kernel_annihilator_arrow C S A B alpha T cone))
        u p));

// Selected genuine cokernel: every colift space is contractible.
symbol ComputationalCokernel
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  : Grpd
≔ `Σ_ Q : τ (Obj C),
   `Σ_ q : τ (Hom C B Q),
   `Σ_ annihilation : τ (@= (Hom C A Q)
      (@comp_fapp0 C A B Q q alpha)
      (@preadditive_hom_zero C S A Q)),
   @Pi_grpd (Obj C) (λ T : τ (Obj C),
     @Pi_grpd (@CokernelCoannihilator C S A B alpha T)
       (λ cone : τ (@CokernelCoannihilator C S A B alpha T),
         IsContr (@CokernelFactorSpace C S A B alpha Q q T cone)));

symbol computational_cokernel_intro
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (Q : τ (Obj C))
  (q : τ (Hom C B Q))
  (annihilation : τ (@= (Hom C A Q)
    (@comp_fapp0 C A B Q q alpha)
    (@preadditive_hom_zero C S A Q)))
  (universal : τ (@Pi_grpd (Obj C) (λ T : τ (Obj C),
    @Pi_grpd (@CokernelCoannihilator C S A B alpha T)
      (λ cone : τ (@CokernelCoannihilator C S A B alpha T),
        IsContr (@CokernelFactorSpace C S A B alpha Q q T cone)))))
  : τ (@ComputationalCokernel C S A B alpha)
≔ @Struct_sigma
    (Obj C)
    (λ Q0 : τ (Obj C),
      `Σ_ q0 : τ (Hom C B Q0),
      `Σ_ annihilation0 : τ (@= (Hom C A Q0)
        (@comp_fapp0 C A B Q0 q0 alpha)
        (@preadditive_hom_zero C S A Q0)),
      @Pi_grpd (Obj C) (λ T : τ (Obj C),
        @Pi_grpd (@CokernelCoannihilator C S A B alpha T)
          (λ cone : τ (@CokernelCoannihilator C S A B alpha T),
            IsContr (@CokernelFactorSpace C S A B alpha Q0 q0 T cone))))
    Q
    (@Struct_sigma
      (Hom C B Q)
      (λ q0 : τ (Hom C B Q),
        `Σ_ annihilation0 : τ (@= (Hom C A Q)
          (@comp_fapp0 C A B Q q0 alpha)
          (@preadditive_hom_zero C S A Q)),
        @Pi_grpd (Obj C) (λ T : τ (Obj C),
          @Pi_grpd (@CokernelCoannihilator C S A B alpha T)
            (λ cone : τ (@CokernelCoannihilator C S A B alpha T),
              IsContr (@CokernelFactorSpace C S A B alpha Q q0 T cone))))
      q
      (@Struct_sigma
        (@= (Hom C A Q)
          (@comp_fapp0 C A B Q q alpha)
          (@preadditive_hom_zero C S A Q))
        (λ _ : τ (@= (Hom C A Q)
          (@comp_fapp0 C A B Q q alpha)
          (@preadditive_hom_zero C S A Q)),
          @Pi_grpd (Obj C) (λ T : τ (Obj C),
            @Pi_grpd (@CokernelCoannihilator C S A B alpha T)
              (λ cone : τ (@CokernelCoannihilator C S A B alpha T),
                IsContr (@CokernelFactorSpace C S A B alpha Q q T cone))))
        annihilation universal));

symbol computational_cokernel_object
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  : τ (Obj C)
≔ sigma_Fst W;

symbol computational_cokernel_morphism
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  : τ (Hom C B (@computational_cokernel_object C S A B alpha W))
≔ sigma_Fst (sigma_Snd W);

symbol computational_cokernel_annihilation
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  : τ (@= (Hom C A (@computational_cokernel_object C S A B alpha W))
      (@comp_fapp0 C A B
        (@computational_cokernel_object C S A B alpha W)
        (@computational_cokernel_morphism C S A B alpha W) alpha)
      (@preadditive_hom_zero C S A
        (@computational_cokernel_object C S A B alpha W)))
≔ sigma_Fst (sigma_Snd (sigma_Snd W));

symbol computational_cokernel_factor_contr
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  : τ (IsContr (@CokernelFactorSpace C S A B alpha
      (@computational_cokernel_object C S A B alpha W)
      (@computational_cokernel_morphism C S A B alpha W) T cone))
≔ (sigma_Snd (sigma_Snd (sigma_Snd W))) T cone;

symbol computational_cokernel_colift
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  : τ (Hom C (@computational_cokernel_object C S A B alpha W) T)
≔ @hfiber_point
    (Hom C (@computational_cokernel_object C S A B alpha W) T)
    (Hom C B T)
    (λ u : τ (Hom C (@computational_cokernel_object C S A B alpha W) T),
      @comp_fapp0 C B
        (@computational_cokernel_object C S A B alpha W) T
        u (@computational_cokernel_morphism C S A B alpha W))
    (@cokernel_coannihilator_arrow C S A B alpha T cone)
    (is_contr_center
      (@computational_cokernel_factor_contr C S A B alpha W T cone));

symbol computational_cokernel_colift_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  : τ (@= (Hom C B T)
      (@comp_fapp0 C B
        (@computational_cokernel_object C S A B alpha W) T
        (@computational_cokernel_colift C S A B alpha W T cone)
        (@computational_cokernel_morphism C S A B alpha W))
      (@cokernel_coannihilator_arrow C S A B alpha T cone))
≔ @hfiber_path
    (Hom C (@computational_cokernel_object C S A B alpha W) T)
    (Hom C B T)
    (λ u : τ (Hom C (@computational_cokernel_object C S A B alpha W) T),
      @comp_fapp0 C B
        (@computational_cokernel_object C S A B alpha W) T
        u (@computational_cokernel_morphism C S A B alpha W))
    (@cokernel_coannihilator_arrow C S A B alpha T cone)
    (is_contr_center
      (@computational_cokernel_factor_contr C S A B alpha W T cone));

symbol computational_cokernel_colift_unique_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  (T : τ (Obj C))
  (cone : τ (@CokernelCoannihilator C S A B alpha T))
  (u : τ (Hom C (@computational_cokernel_object C S A B alpha W) T))
  (p : τ (@= (Hom C B T)
    (@comp_fapp0 C B
      (@computational_cokernel_object C S A B alpha W) T
      u (@computational_cokernel_morphism C S A B alpha W))
    (@cokernel_coannihilator_arrow C S A B alpha T cone)))
  : τ (@= (Hom C (@computational_cokernel_object C S A B alpha W) T)
      (@computational_cokernel_colift C S A B alpha W T cone) u)
≔ @eq_ap
    (@CokernelFactorSpace C S A B alpha
      (@computational_cokernel_object C S A B alpha W)
      (@computational_cokernel_morphism C S A B alpha W) T cone)
    (Hom C (@computational_cokernel_object C S A B alpha W) T)
    (λ factor : τ (@CokernelFactorSpace C S A B alpha
      (@computational_cokernel_object C S A B alpha W)
      (@computational_cokernel_morphism C S A B alpha W) T cone),
      @hfiber_point
        (Hom C (@computational_cokernel_object C S A B alpha W) T)
        (Hom C B T)
        (λ v : τ (Hom C
          (@computational_cokernel_object C S A B alpha W) T),
          @comp_fapp0 C B
            (@computational_cokernel_object C S A B alpha W) T
            v (@computational_cokernel_morphism C S A B alpha W))
        (@cokernel_coannihilator_arrow C S A B alpha T cone)
        factor)
    (is_contr_center
      (@computational_cokernel_factor_contr C S A B alpha W T cone))
    (@Struct_sigma
      (Hom C (@computational_cokernel_object C S A B alpha W) T)
      (λ v : τ (Hom C (@computational_cokernel_object C S A B alpha W) T),
        @= (Hom C B T)
          (@comp_fapp0 C B
            (@computational_cokernel_object C S A B alpha W) T
            v (@computational_cokernel_morphism C S A B alpha W))
          (@cokernel_coannihilator_arrow C S A B alpha T cone))
      u p)
    (is_contr_path
      (@computational_cokernel_factor_contr C S A B alpha W T cone)
      (@Struct_sigma
        (Hom C (@computational_cokernel_object C S A B alpha W) T)
        (λ v : τ (Hom C (@computational_cokernel_object C S A B alpha W) T),
          @= (Hom C B T)
            (@comp_fapp0 C B
              (@computational_cokernel_object C S A B alpha W) T
              v (@computational_cokernel_morphism C S A B alpha W))
            (@cokernel_coannihilator_arrow C S A B alpha T cone))
        u p));

// Proposition-valued ordinary existence views.
symbol Kernel
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  : Grpd
≔ @Trunc_grpd trunc_minus_one (@ComputationalKernel C S A B alpha);

symbol Cokernel
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (alpha : τ (Hom C A B))
  : Grpd
≔ @Trunc_grpd trunc_minus_one (@ComputationalCokernel C S A B alpha);

symbol computational_kernel_is_kernel
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  : τ (@Kernel C S A B alpha)
≔ @trunc_intro trunc_minus_one (@ComputationalKernel C S A B alpha) W;

symbol computational_cokernel_is_cokernel
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  : τ (@Cokernel C S A B alpha)
≔ @trunc_intro trunc_minus_one (@ComputationalCokernel C S A B alpha) W;

// Whole selected capabilities over every arrow.
symbol HasComputationalKernels
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ alpha : τ (Hom C A B),
        @ComputationalKernel C S A B alpha)));

symbol HasComputationalCokernels
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ alpha : τ (Hom C A B),
        @ComputationalCokernel C S A B alpha)));

symbol HasKernels
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ alpha : τ (Hom C A B),
        @Kernel C S A B alpha)));

symbol HasCokernels
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ alpha : τ (Hom C A B),
        @Cokernel C S A B alpha)));

symbol computational_kernels_are_kernels
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S))
  : τ (@HasKernels C S)
≔ λ A : τ (Obj C), λ B : τ (Obj C), λ alpha : τ (Hom C A B),
    @computational_kernel_is_kernel C S A B alpha (W A B alpha);

symbol computational_cokernels_are_cokernels
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalCokernels C S))
  : τ (@HasCokernels C S)
≔ λ A : τ (Obj C), λ B : τ (Obj C), λ alpha : τ (Hom C A B),
    @computational_cokernel_is_cokernel C S A B alpha (W A B alpha);

// Selected computational pre-Abelian structure on existing additive data.
symbol PreAbelianCategory
  [C : Cat]
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  : Grpd
≔ `Σ_ A : τ (@AdditiveCategory C P t),
   @Product_grpd
      (@HasComputationalKernels C (@additive_preadditive C P t A))
      (@HasComputationalCokernels C (@additive_preadditive C P t A));

symbol preabelian_category_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C P t))
  (K : τ (@HasComputationalKernels C (@additive_preadditive C P t A)))
  (Q : τ (@HasComputationalCokernels C (@additive_preadditive C P t A)))
  : τ (@PreAbelianCategory C P t)
≔ @Struct_sigma
    (@AdditiveCategory C P t)
    (λ A0 : τ (@AdditiveCategory C P t),
      @Product_grpd
        (@HasComputationalKernels C (@additive_preadditive C P t A0))
        (@HasComputationalCokernels C (@additive_preadditive C P t A0)))
    A (@Product_pair_grpd _ _ K Q);

symbol preabelian_additive
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@PreAbelianCategory C P t))
  : τ (@AdditiveCategory C P t)
≔ sigma_Fst A;

symbol preabelian_kernels
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@PreAbelianCategory C P t))
  : τ (@HasComputationalKernels C
      (@additive_preadditive C P t (@preabelian_additive C P t A)))
≔ sigma_Fst (sigma_Snd A);

symbol preabelian_cokernels
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@PreAbelianCategory C P t))
  : τ (@HasComputationalCokernels C
      (@additive_preadditive C P t (@preabelian_additive C P t A)))
≔ sigma_Snd (sigma_Snd A);
