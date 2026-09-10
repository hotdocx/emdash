/* Direct row-universal construction: retain a chosen factor, derive uniqueness. */
require open emdash.emdash3_2_abelian_categories;
require open emdash.emdash3_2_eq1_evidence_property;

// Over a set-valued target, a fibre path is determined by its domain path.
symbol hfiber_set_target_path
  [A B : Grpd] (Bset : τ (IsSetGrpd B))
  [f : τ A → τ B] [b : τ B]
  (u v : τ (@HFiber A B f b))
  (p : τ (@= A (sigma_Fst u) (sigma_Fst v)))
  : τ (@= (@HFiber A B f b) u v)
≔ @sigma_path_decode A (λ a : τ A, @= B (f a) b) u v
    (@Struct_sigma (@= A (sigma_Fst u) (sigma_Fst v))
      (λ q : τ (@= A (sigma_Fst u) (sigma_Fst v)),
        @PathOver A (λ a : τ A, @= B (f a) b)
          (sigma_Fst u) (sigma_Fst v) q (sigma_Snd u) (sigma_Snd v))
      p
      (@prop_family_pathover A (λ a : τ A, @= B (f a) b)
        (λ a : τ A, Bset (f a) b)
        (sigma_Fst u) (sigma_Fst v) p (sigma_Snd u) (sigma_Snd v)));

// An injective function's inhabited fibre contracts at its supplied point.
symbol hfiber_contr_from_cancellation
  [A B : Grpd] (Bset : τ (IsSetGrpd B))
  (f : τ A → τ B)
  (cancel : Π x : τ A, Π y : τ A, τ (@= B (f x) (f y)) → τ (@= A x y))
  (b : τ B) (centre : τ (@HFiber A B f b))
  : τ (IsContr (@HFiber A B f b))
≔ @Struct_sigma (@HFiber A B f b)
    (λ w : τ (@HFiber A B f b),
      @Pi_grpd (@HFiber A B f b) (λ u : τ (@HFiber A B f b),
        @= (@HFiber A B f b) w u))
    centre
    (λ u : τ (@HFiber A B f b),
      @hfiber_set_target_path A B Bset f b centre u
        (cancel (sigma_Fst centre) (sigma_Fst u)
          (@eq_trans B (f (sigma_Fst centre)) b (f (sigma_Fst u))
            (sigma_Snd centre) (@eq_sym B (f (sigma_Fst u)) b (sigma_Snd u)))));

symbol kernel_factor_contr_from_monic
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B K : τ (Obj C)] [alpha : τ (Hom C A B)]
  [kappa : τ (Hom C K A)] (monic : τ (@IsMonic C K A kappa))
  [T : τ (Obj C)] [cone : τ (@WeakKernelAnnihilator C S A B alpha T)]
  (centre : τ (@KernelFactorSpace C S A B alpha K kappa T cone))
  : τ (IsContr (@KernelFactorSpace C S A B alpha K kappa T cone))
≔ @hfiber_contr_from_cancellation (Hom C T K) (Hom C T A)
    (@preadditive_hom_is_set C S T A)
    (λ u : τ (Hom C T K), @comp_fapp0 C T K A kappa u)
    (monic T)
    (@weak_kernel_annihilator_arrow C S A B alpha T cone) centre;

symbol cokernel_factor_contr_from_epic
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B Q : τ (Obj C)] [alpha : τ (Hom C A B)]
  [q : τ (Hom C B Q)] (epic : τ (@IsEpic C B Q q))
  [T : τ (Obj C)] [cocone : τ (@CokernelCoannihilator C S A B alpha T)]
  (centre : τ (@CokernelFactorSpace C S A B alpha Q q T cocone))
  : τ (IsContr (@CokernelFactorSpace C S A B alpha Q q T cocone))
≔ @hfiber_contr_from_cancellation (Hom C Q T) (Hom C B T)
    (@preadditive_hom_is_set C S B T)
    (λ u : τ (Hom C Q T), @comp_fapp0 C B Q T u q)
    (epic T)
    (@cokernel_coannihilator_arrow C S A B alpha T cocone) centre;

// Package the chosen all-test factors; cancellation supplies their uniqueness.
symbol computational_kernel_from_monic_factors
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] [alpha : τ (Hom C A B)]
  (K : τ (Obj C)) (kappa : τ (Hom C K A))
  (zero : τ (@= (Hom C K B) (@comp_fapp0 C K A B alpha kappa)
    (@preadditive_hom_zero C S K B)))
  (monic : τ (@IsMonic C K A kappa))
  (factors : Π T : τ (Obj C), Π cone : τ (@WeakKernelAnnihilator C S A B alpha T),
    τ (@KernelFactorSpace C S A B alpha K kappa T cone))
  : τ (@ComputationalKernel C S A B alpha)
≔ @computational_kernel_intro C S A B alpha K kappa zero
    (λ T : τ (Obj C), λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
      @kernel_factor_contr_from_monic C S A B K alpha kappa monic T cone
        (factors T cone));

symbol computational_cokernel_from_epic_factors
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] [alpha : τ (Hom C A B)]
  (Q : τ (Obj C)) (q : τ (Hom C B Q))
  (zero : τ (@= (Hom C A Q) (@comp_fapp0 C A B Q q alpha)
    (@preadditive_hom_zero C S A Q)))
  (epic : τ (@IsEpic C B Q q))
  (factors : Π T : τ (Obj C), Π cocone : τ (@CokernelCoannihilator C S A B alpha T),
    τ (@CokernelFactorSpace C S A B alpha Q q T cocone))
  : τ (@ComputationalCokernel C S A B alpha)
≔ @computational_cokernel_intro C S A B alpha Q q zero
    (λ T : τ (Obj C), λ cocone : τ (@CokernelCoannihilator C S A B alpha T),
      @cokernel_factor_contr_from_epic C S A B Q alpha q epic T cocone
        (factors T cocone));
