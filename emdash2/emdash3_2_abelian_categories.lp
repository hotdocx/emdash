/*
  Computational normality and the generic Abelian package.

  Monicity and epicity are cancellation properties of the existing Hom
  actions. Contractible kernel/cokernel factor spaces prove the selected
  structural arrows monic/epic. Normal-monomorphism lifts and
  normal-epimorphism colifts are again internal HFiber spaces; their centres,
  fibre paths, and contractions expose selected factors, reconstruction, and
  uniqueness. No manual diagram grammar or runtime rule is introduced.
*/

require open emdash.emdash3_2_kernels_cokernels;

symbol IsMonic
  [C : Cat]
  [A B : τ (Obj C)]
  (m : τ (Hom C A B))
  : Grpd
≔ @Pi_grpd (Obj C) (λ T : τ (Obj C),
    @Pi_grpd (Hom C T A) (λ u : τ (Hom C T A),
      @Pi_grpd (Hom C T A) (λ v : τ (Hom C T A),
        @Function_grpd
          (@= (Hom C T B)
            (@comp_fapp0 C T A B m u)
            (@comp_fapp0 C T A B m v))
          (@= (Hom C T A) u v))));

symbol IsEpic
  [C : Cat]
  [A B : τ (Obj C)]
  (e : τ (Hom C A B))
  : Grpd
≔ @Pi_grpd (Obj C) (λ T : τ (Obj C),
    @Pi_grpd (Hom C B T) (λ u : τ (Hom C B T),
      @Pi_grpd (Hom C B T) (λ v : τ (Hom C B T),
        @Function_grpd
          (@= (Hom C A T)
            (@comp_fapp0 C A B T u e)
            (@comp_fapp0 C A B T v e))
          (@= (Hom C B T) u v))));

symbol computational_kernel_monic_cone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  (T : τ (Obj C))
  (u : τ (Hom C T (@computational_kernel_object C S A B alpha W)))
  : τ (@WeakKernelAnnihilator C S A B alpha T)
≔ @Struct_sigma
    (Hom C T A)
    (λ tau : τ (Hom C T A),
      @= (Hom C T B)
        (@comp_fapp0 C T A B alpha tau)
        (@preadditive_hom_zero C S T B))
    (@comp_fapp0 C T
      (@computational_kernel_object C S A B alpha W) A
      (@computational_kernel_morphism C S A B alpha W) u)
    (@eq_trans
      (Hom C T B)
      (@comp_fapp0 C T A B alpha
        (@comp_fapp0 C T
          (@computational_kernel_object C S A B alpha W) A
          (@computational_kernel_morphism C S A B alpha W) u))
      (@comp_fapp0 C T
        (@computational_kernel_object C S A B alpha W) B
        (@comp_fapp0 C
          (@computational_kernel_object C S A B alpha W) A B
          alpha (@computational_kernel_morphism C S A B alpha W)) u)
      (@preadditive_hom_zero C S T B)
      (@comp_assoc C T
        (@computational_kernel_object C S A B alpha W) A B
        alpha (@computational_kernel_morphism C S A B alpha W) u)
      (@eq_trans
        (Hom C T B)
        (@comp_fapp0 C T
          (@computational_kernel_object C S A B alpha W) B
          (@comp_fapp0 C
            (@computational_kernel_object C S A B alpha W) A B
            alpha (@computational_kernel_morphism C S A B alpha W)) u)
        (@comp_fapp0 C T
          (@computational_kernel_object C S A B alpha W) B
          (@preadditive_hom_zero C S
            (@computational_kernel_object C S A B alpha W) B) u)
        (@preadditive_hom_zero C S T B)
        (@eq_ap
          (Hom C (@computational_kernel_object C S A B alpha W) B)
          (Hom C T B)
          (λ z : τ (Hom C
              (@computational_kernel_object C S A B alpha W) B),
            @comp_fapp0 C T
              (@computational_kernel_object C S A B alpha W) B z u)
          _ _
          (@computational_kernel_annihilation C S A B alpha W))
        (@preadditive_comp_zero_left_path C S T
          (@computational_kernel_object C S A B alpha W) B u)));

symbol computational_kernel_morphism_is_monic
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B alpha))
  : τ (@IsMonic C
      (@computational_kernel_object C S A B alpha W) A
      (@computational_kernel_morphism C S A B alpha W))
≔ λ T : τ (Obj C),
   λ u : τ (Hom C T (@computational_kernel_object C S A B alpha W)),
   λ v : τ (Hom C T (@computational_kernel_object C S A B alpha W)),
   λ p : τ (@= (Hom C T A)
      (@comp_fapp0 C T
        (@computational_kernel_object C S A B alpha W) A
        (@computational_kernel_morphism C S A B alpha W) u)
      (@comp_fapp0 C T
        (@computational_kernel_object C S A B alpha W) A
        (@computational_kernel_morphism C S A B alpha W) v)),
   @eq_trans
      (Hom C T (@computational_kernel_object C S A B alpha W))
      u
      (@computational_kernel_lift C S A B alpha W T
        (@computational_kernel_monic_cone C S A B alpha W T u))
      v
      (@eq_sym _ _ _
        (@computational_kernel_lift_unique_path C S A B alpha W T
          (@computational_kernel_monic_cone C S A B alpha W T u)
          u (@eq_refl _
            (@comp_fapp0 C T
              (@computational_kernel_object C S A B alpha W) A
              (@computational_kernel_morphism C S A B alpha W) u))))
      (@computational_kernel_lift_unique_path C S A B alpha W T
        (@computational_kernel_monic_cone C S A B alpha W T u)
        v (@eq_sym _ _ _ p));

symbol computational_cokernel_epic_cone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  (T : τ (Obj C))
  (u : τ (Hom C (@computational_cokernel_object C S A B alpha W) T))
  : τ (@CokernelCoannihilator C S A B alpha T)
≔ @Struct_sigma
    (Hom C B T)
    (λ tau : τ (Hom C B T),
      @= (Hom C A T)
        (@comp_fapp0 C A B T tau alpha)
        (@preadditive_hom_zero C S A T))
    (@comp_fapp0 C B
      (@computational_cokernel_object C S A B alpha W) T u
      (@computational_cokernel_morphism C S A B alpha W))
    (@eq_trans
      (Hom C A T)
      (@comp_fapp0 C A B T
        (@comp_fapp0 C B
          (@computational_cokernel_object C S A B alpha W) T u
          (@computational_cokernel_morphism C S A B alpha W)) alpha)
      (@comp_fapp0 C A
        (@computational_cokernel_object C S A B alpha W) T u
        (@comp_fapp0 C A B
          (@computational_cokernel_object C S A B alpha W)
          (@computational_cokernel_morphism C S A B alpha W) alpha))
      (@preadditive_hom_zero C S A T)
      (@eq_sym _ _ _
        (@comp_assoc C A B
          (@computational_cokernel_object C S A B alpha W) T
          u (@computational_cokernel_morphism C S A B alpha W) alpha))
      (@eq_trans
        (Hom C A T)
        (@comp_fapp0 C A
          (@computational_cokernel_object C S A B alpha W) T u
          (@comp_fapp0 C A B
            (@computational_cokernel_object C S A B alpha W)
            (@computational_cokernel_morphism C S A B alpha W) alpha))
        (@comp_fapp0 C A
          (@computational_cokernel_object C S A B alpha W) T u
          (@preadditive_hom_zero C S A
            (@computational_cokernel_object C S A B alpha W)))
        (@preadditive_hom_zero C S A T)
        (@eq_ap
          (Hom C A (@computational_cokernel_object C S A B alpha W))
          (Hom C A T)
          (λ z : τ (Hom C A
              (@computational_cokernel_object C S A B alpha W)),
            @comp_fapp0 C A
              (@computational_cokernel_object C S A B alpha W) T u z)
          _ _
          (@computational_cokernel_annihilation C S A B alpha W))
        (@preadditive_comp_zero_right_path C S A
          (@computational_cokernel_object C S A B alpha W) T u)));

symbol computational_cokernel_morphism_is_epic
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B alpha))
  : τ (@IsEpic C B
      (@computational_cokernel_object C S A B alpha W)
      (@computational_cokernel_morphism C S A B alpha W))
≔ λ T : τ (Obj C),
   λ u : τ (Hom C
      (@computational_cokernel_object C S A B alpha W) T),
   λ v : τ (Hom C
      (@computational_cokernel_object C S A B alpha W) T),
   λ p : τ (@= (Hom C B T)
      (@comp_fapp0 C B
        (@computational_cokernel_object C S A B alpha W) T u
        (@computational_cokernel_morphism C S A B alpha W))
      (@comp_fapp0 C B
        (@computational_cokernel_object C S A B alpha W) T v
        (@computational_cokernel_morphism C S A B alpha W))),
   @eq_trans
      (Hom C (@computational_cokernel_object C S A B alpha W) T)
      u
      (@computational_cokernel_colift C S A B alpha W T
        (@computational_cokernel_epic_cone C S A B alpha W T u))
      v
      (@eq_sym _ _ _
        (@computational_cokernel_colift_unique_path C S A B alpha W T
          (@computational_cokernel_epic_cone C S A B alpha W T u)
          u (@eq_refl _
            (@comp_fapp0 C B
              (@computational_cokernel_object C S A B alpha W) T u
              (@computational_cokernel_morphism C S A B alpha W)))))
      (@computational_cokernel_colift_unique_path C S A B alpha W T
        (@computational_cokernel_epic_cone C S A B alpha W T u)
        v (@eq_sym _ _ _ p));

// Tests tau : T -> B annihilated by the selected cokernel of m.
symbol NormalMonoTest
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (m : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B m))
  (T : τ (Obj C))
  : Grpd
≔ @WeakKernelAnnihilator C S B
    (@computational_cokernel_object C S A B m W)
    (@computational_cokernel_morphism C S A B m W) T;

// Lifts u : T -> A satisfying m o u = tau.
symbol NormalMonoLiftSpace
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (m : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B m))
  (T : τ (Obj C))
  (test : τ (@NormalMonoTest C S A B m W T))
  : Grpd
≔ @HFiber
    (Hom C T A)
    (Hom C T B)
    (λ u : τ (Hom C T A), @comp_fapp0 C T A B m u)
    (@weak_kernel_annihilator_arrow C S B
      (@computational_cokernel_object C S A B m W)
      (@computational_cokernel_morphism C S A B m W) T test);

// Every monomorphism has contractible lift spaces for cokernel-zero tests.
symbol HasLiftsAlongMonomorphisms
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  (Q : τ (@HasComputationalCokernels C S))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ m : τ (Hom C A B),
        @Pi_grpd (@IsMonic C A B m) (λ _ : τ (@IsMonic C A B m),
          @Pi_grpd (Obj C) (λ T : τ (Obj C),
            @Pi_grpd (@NormalMonoTest C S A B m (Q A B m) T)
              (λ test : τ _,
                IsContr (@NormalMonoLiftSpace C S A B m
                  (Q A B m) T test)))))));

symbol normal_mono_lift_contr
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [Q : τ (@HasComputationalCokernels C S)]
  (N : τ (@HasLiftsAlongMonomorphisms C S Q))
  [A B : τ (Obj C)]
  [m : τ (Hom C A B)]
  (monic : τ (@IsMonic C A B m))
  (T : τ (Obj C))
  (test : τ (@NormalMonoTest C S A B m (Q A B m) T))
  : τ (IsContr (@NormalMonoLiftSpace C S A B m (Q A B m) T test))
≔ N A B m monic T test;

symbol lift_along_monomorphism
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [Q : τ (@HasComputationalCokernels C S)]
  (N : τ (@HasLiftsAlongMonomorphisms C S Q))
  [A B : τ (Obj C)]
  [m : τ (Hom C A B)]
  (monic : τ (@IsMonic C A B m))
  (T : τ (Obj C))
  (test : τ (@NormalMonoTest C S A B m (Q A B m) T))
  : τ (Hom C T A)
≔ @hfiber_point
    (Hom C T A) (Hom C T B)
    (λ u : τ (Hom C T A), @comp_fapp0 C T A B m u)
    (@weak_kernel_annihilator_arrow C S B
      (@computational_cokernel_object C S A B m (Q A B m))
      (@computational_cokernel_morphism C S A B m (Q A B m)) T test)
    (is_contr_center (@normal_mono_lift_contr C S Q N A B m monic T test));

symbol lift_along_monomorphism_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [Q : τ (@HasComputationalCokernels C S)]
  (N : τ (@HasLiftsAlongMonomorphisms C S Q))
  [A B : τ (Obj C)]
  [m : τ (Hom C A B)]
  (monic : τ (@IsMonic C A B m))
  (T : τ (Obj C))
  (test : τ (@NormalMonoTest C S A B m (Q A B m) T))
  : τ (@= (Hom C T B)
      (@comp_fapp0 C T A B m
        (@lift_along_monomorphism C S Q N A B m monic T test))
      (@weak_kernel_annihilator_arrow C S B
        (@computational_cokernel_object C S A B m (Q A B m))
        (@computational_cokernel_morphism C S A B m (Q A B m)) T test))
≔ @hfiber_path
    (Hom C T A) (Hom C T B)
    (λ u : τ (Hom C T A), @comp_fapp0 C T A B m u)
    (@weak_kernel_annihilator_arrow C S B
      (@computational_cokernel_object C S A B m (Q A B m))
      (@computational_cokernel_morphism C S A B m (Q A B m)) T test)
    (is_contr_center (@normal_mono_lift_contr C S Q N A B m monic T test));

symbol lift_along_monomorphism_unique_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [Q : τ (@HasComputationalCokernels C S)]
  (N : τ (@HasLiftsAlongMonomorphisms C S Q))
  [A B : τ (Obj C)]
  [m : τ (Hom C A B)]
  (monic : τ (@IsMonic C A B m))
  (T : τ (Obj C))
  (test : τ (@NormalMonoTest C S A B m (Q A B m) T))
  (u : τ (Hom C T A))
  (p : τ (@= (Hom C T B)
    (@comp_fapp0 C T A B m u)
    (@weak_kernel_annihilator_arrow C S B
      (@computational_cokernel_object C S A B m (Q A B m))
      (@computational_cokernel_morphism C S A B m (Q A B m)) T test)))
  : τ (@= (Hom C T A)
      (@lift_along_monomorphism C S Q N A B m monic T test) u)
≔ @eq_ap
    (@NormalMonoLiftSpace C S A B m (Q A B m) T test)
    (Hom C T A)
    (λ factor : τ (@NormalMonoLiftSpace C S A B m (Q A B m) T test),
      @hfiber_point
        (Hom C T A) (Hom C T B)
        (λ v : τ (Hom C T A), @comp_fapp0 C T A B m v)
        (@weak_kernel_annihilator_arrow C S B
          (@computational_cokernel_object C S A B m (Q A B m))
          (@computational_cokernel_morphism C S A B m (Q A B m)) T test)
        factor)
    (is_contr_center (@normal_mono_lift_contr C S Q N A B m monic T test))
    (@Struct_sigma
      (Hom C T A)
      (λ v : τ (Hom C T A),
        @= (Hom C T B)
          (@comp_fapp0 C T A B m v)
          (@weak_kernel_annihilator_arrow C S B
            (@computational_cokernel_object C S A B m (Q A B m))
            (@computational_cokernel_morphism C S A B m (Q A B m)) T test))
      u p)
    (is_contr_path
      (@normal_mono_lift_contr C S Q N A B m monic T test)
      (@Struct_sigma
        (Hom C T A)
        (λ v : τ (Hom C T A),
          @= (Hom C T B)
            (@comp_fapp0 C T A B m v)
            (@weak_kernel_annihilator_arrow C S B
              (@computational_cokernel_object C S A B m (Q A B m))
              (@computational_cokernel_morphism C S A B m (Q A B m)) T test))
        u p));

// Tests tau : A -> T annihilating the selected kernel of e.
symbol NormalEpiTest
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (e : τ (Hom C A B))
  (W : τ (@ComputationalKernel C S A B e))
  (T : τ (Obj C))
  : Grpd
≔ @CokernelCoannihilator C S
    (@computational_kernel_object C S A B e W) A
    (@computational_kernel_morphism C S A B e W) T;

// Colifts u : B -> T satisfying u o e = tau.
symbol NormalEpiColiftSpace
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [A B : τ (Obj C)]
  (e : τ (Hom C A B))
  (W : τ (@ComputationalKernel C S A B e))
  (T : τ (Obj C))
  (test : τ (@NormalEpiTest C S A B e W T))
  : Grpd
≔ @HFiber
    (Hom C B T)
    (Hom C A T)
    (λ u : τ (Hom C B T), @comp_fapp0 C A B T u e)
    (@cokernel_coannihilator_arrow C S
      (@computational_kernel_object C S A B e W) A
      (@computational_kernel_morphism C S A B e W) T test);

symbol HasColiftsAlongEpimorphisms
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  (K : τ (@HasComputationalKernels C S))
  : Grpd
≔ @Pi_grpd (Obj C) (λ A : τ (Obj C),
    @Pi_grpd (Obj C) (λ B : τ (Obj C),
      @Pi_grpd (Hom C A B) (λ e : τ (Hom C A B),
        @Pi_grpd (@IsEpic C A B e) (λ _ : τ (@IsEpic C A B e),
          @Pi_grpd (Obj C) (λ T : τ (Obj C),
            @Pi_grpd (@NormalEpiTest C S A B e (K A B e) T)
              (λ test : τ _,
                IsContr (@NormalEpiColiftSpace C S A B e
                  (K A B e) T test)))))));

symbol normal_epi_colift_contr
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [K : τ (@HasComputationalKernels C S)]
  (N : τ (@HasColiftsAlongEpimorphisms C S K))
  [A B : τ (Obj C)]
  [e : τ (Hom C A B)]
  (epic : τ (@IsEpic C A B e))
  (T : τ (Obj C))
  (test : τ (@NormalEpiTest C S A B e (K A B e) T))
  : τ (IsContr (@NormalEpiColiftSpace C S A B e (K A B e) T test))
≔ N A B e epic T test;

symbol colift_along_epimorphism
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [K : τ (@HasComputationalKernels C S)]
  (N : τ (@HasColiftsAlongEpimorphisms C S K))
  [A B : τ (Obj C)]
  [e : τ (Hom C A B)]
  (epic : τ (@IsEpic C A B e))
  (T : τ (Obj C))
  (test : τ (@NormalEpiTest C S A B e (K A B e) T))
  : τ (Hom C B T)
≔ @hfiber_point
    (Hom C B T) (Hom C A T)
    (λ u : τ (Hom C B T), @comp_fapp0 C A B T u e)
    (@cokernel_coannihilator_arrow C S
      (@computational_kernel_object C S A B e (K A B e)) A
      (@computational_kernel_morphism C S A B e (K A B e)) T test)
    (is_contr_center (@normal_epi_colift_contr C S K N A B e epic T test));

symbol colift_along_epimorphism_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [K : τ (@HasComputationalKernels C S)]
  (N : τ (@HasColiftsAlongEpimorphisms C S K))
  [A B : τ (Obj C)]
  [e : τ (Hom C A B)]
  (epic : τ (@IsEpic C A B e))
  (T : τ (Obj C))
  (test : τ (@NormalEpiTest C S A B e (K A B e) T))
  : τ (@= (Hom C A T)
      (@comp_fapp0 C A B T
        (@colift_along_epimorphism C S K N A B e epic T test) e)
      (@cokernel_coannihilator_arrow C S
        (@computational_kernel_object C S A B e (K A B e)) A
        (@computational_kernel_morphism C S A B e (K A B e)) T test))
≔ @hfiber_path
    (Hom C B T) (Hom C A T)
    (λ u : τ (Hom C B T), @comp_fapp0 C A B T u e)
    (@cokernel_coannihilator_arrow C S
      (@computational_kernel_object C S A B e (K A B e)) A
      (@computational_kernel_morphism C S A B e (K A B e)) T test)
    (is_contr_center (@normal_epi_colift_contr C S K N A B e epic T test));

symbol colift_along_epimorphism_unique_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [K : τ (@HasComputationalKernels C S)]
  (N : τ (@HasColiftsAlongEpimorphisms C S K))
  [A B : τ (Obj C)]
  [e : τ (Hom C A B)]
  (epic : τ (@IsEpic C A B e))
  (T : τ (Obj C))
  (test : τ (@NormalEpiTest C S A B e (K A B e) T))
  (u : τ (Hom C B T))
  (p : τ (@= (Hom C A T)
    (@comp_fapp0 C A B T u e)
    (@cokernel_coannihilator_arrow C S
      (@computational_kernel_object C S A B e (K A B e)) A
      (@computational_kernel_morphism C S A B e (K A B e)) T test)))
  : τ (@= (Hom C B T)
      (@colift_along_epimorphism C S K N A B e epic T test) u)
≔ @eq_ap
    (@NormalEpiColiftSpace C S A B e (K A B e) T test)
    (Hom C B T)
    (λ factor : τ (@NormalEpiColiftSpace C S A B e (K A B e) T test),
      @hfiber_point
        (Hom C B T) (Hom C A T)
        (λ v : τ (Hom C B T), @comp_fapp0 C A B T v e)
        (@cokernel_coannihilator_arrow C S
          (@computational_kernel_object C S A B e (K A B e)) A
          (@computational_kernel_morphism C S A B e (K A B e)) T test)
        factor)
    (is_contr_center (@normal_epi_colift_contr C S K N A B e epic T test))
    (@Struct_sigma
      (Hom C B T)
      (λ v : τ (Hom C B T),
        @= (Hom C A T)
          (@comp_fapp0 C A B T v e)
          (@cokernel_coannihilator_arrow C S
            (@computational_kernel_object C S A B e (K A B e)) A
            (@computational_kernel_morphism C S A B e (K A B e)) T test))
      u p)
    (is_contr_path
      (@normal_epi_colift_contr C S K N A B e epic T test)
      (@Struct_sigma
        (Hom C B T)
        (λ v : τ (Hom C B T),
          @= (Hom C A T)
            (@comp_fapp0 C A B T v e)
            (@cokernel_coannihilator_arrow C S
              (@computational_kernel_object C S A B e (K A B e)) A
              (@computational_kernel_morphism C S A B e (K A B e)) T test))
        u p));

// Selected computational Abelian structure on existing pre-Abelian data.
symbol ComputationalAbelianCategory
  [C : Cat]
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  : Grpd
≔ `Σ_ A : τ (@PreAbelianCategory C P t),
   @Product_grpd
      (@HasLiftsAlongMonomorphisms C
        (@additive_preadditive C P t (@preabelian_additive C P t A))
        (@preabelian_cokernels C P t A))
      (@HasColiftsAlongEpimorphisms C
        (@additive_preadditive C P t (@preabelian_additive C P t A))
        (@preabelian_kernels C P t A));

symbol computational_abelian_category_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@additive_preadditive C P t (@preabelian_additive C P t A))
    (@preabelian_cokernels C P t A)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@additive_preadditive C P t (@preabelian_additive C P t A))
    (@preabelian_kernels C P t A)))
  : τ (@ComputationalAbelianCategory C P t)
≔ @Struct_sigma
    (@PreAbelianCategory C P t)
    (λ A0 : τ (@PreAbelianCategory C P t),
      @Product_grpd
        (@HasLiftsAlongMonomorphisms C
          (@additive_preadditive C P t (@preabelian_additive C P t A0))
          (@preabelian_cokernels C P t A0))
        (@HasColiftsAlongEpimorphisms C
          (@additive_preadditive C P t (@preabelian_additive C P t A0))
          (@preabelian_kernels C P t A0)))
    A (@Product_pair_grpd _ _ M E);

symbol computational_abelian_preabelian
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@PreAbelianCategory C P t)
≔ sigma_Fst A;

symbol computational_abelian_mono_lifts
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@HasLiftsAlongMonomorphisms C
      (@additive_preadditive C P t
        (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t A)))
      (@preabelian_cokernels C P t
        (@computational_abelian_preabelian C P t A)))
≔ sigma_Fst (sigma_Snd A);

symbol computational_abelian_epi_colifts
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (A : τ (@ComputationalAbelianCategory C P t))
  : τ (@HasColiftsAlongEpimorphisms C
      (@additive_preadditive C P t
        (@preabelian_additive C P t
          (@computational_abelian_preabelian C P t A)))
      (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t A)))
≔ sigma_Snd (sigma_Snd A);
