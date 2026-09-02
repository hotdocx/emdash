/*
  Derived image, coimage, and their canonical comparison.

  Coim(f) is the selected cokernel of Ker(f); Im(f) is the selected kernel of
  Coker(f). Cokernel universality first constructs the coimage coastriction,
  cancellation along the epic coimage projection proves it annihilated by
  Coker(f), and kernel universality then constructs the comparison. The final
  path factors f through projection, comparison, and embedding. No primitive
  image algorithm, isomorphism, or runtime rule is introduced.
*/

require open emdash.emdash3_2_abelian_categories;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

// A monomorphism has zero selected kernel embedding.
symbol monic_kernel_morphism_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [m : τ (Hom C A B)]
  (W : τ (@ComputationalKernel C S A B m))
  (monic : τ (@IsMonic C A B m))
  : τ (@= (Hom C (@computational_kernel_object C S A B m W) A)
      (@computational_kernel_morphism C S A B m W)
      (@preadditive_hom_zero C S
        (@computational_kernel_object C S A B m W) A))
≔ monic
    (@computational_kernel_object C S A B m W)
    (@computational_kernel_morphism C S A B m W)
    (@preadditive_hom_zero C S
      (@computational_kernel_object C S A B m W) A)
    (@eq_trans
      (Hom C (@computational_kernel_object C S A B m W) B)
      (@comp_fapp0 C
        (@computational_kernel_object C S A B m W) A B m
        (@computational_kernel_morphism C S A B m W))
      (@preadditive_hom_zero C S
        (@computational_kernel_object C S A B m W) B)
      (@comp_fapp0 C
        (@computational_kernel_object C S A B m W) A B m
        (@preadditive_hom_zero C S
          (@computational_kernel_object C S A B m W) A))
      (@computational_kernel_annihilation C S A B m W)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_right_path C S
          (@computational_kernel_object C S A B m W) A B m)));

// An epimorphism has zero selected cokernel projection.
symbol epic_cokernel_morphism_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [e : τ (Hom C A B)]
  (W : τ (@ComputationalCokernel C S A B e))
  (epic : τ (@IsEpic C A B e))
  : τ (@= (Hom C B (@computational_cokernel_object C S A B e W))
      (@computational_cokernel_morphism C S A B e W)
      (@preadditive_hom_zero C S B
        (@computational_cokernel_object C S A B e W)))
≔ epic
    (@computational_cokernel_object C S A B e W)
    (@computational_cokernel_morphism C S A B e W)
    (@preadditive_hom_zero C S B
      (@computational_cokernel_object C S A B e W))
    (@eq_trans
      (Hom C A (@computational_cokernel_object C S A B e W))
      (@comp_fapp0 C A B
        (@computational_cokernel_object C S A B e W)
        (@computational_cokernel_morphism C S A B e W) e)
      (@preadditive_hom_zero C S A
        (@computational_cokernel_object C S A B e W))
      (@comp_fapp0 C A B
        (@computational_cokernel_object C S A B e W)
        (@preadditive_hom_zero C S B
          (@computational_cokernel_object C S A B e W)) e)
      (@computational_cokernel_annihilation C S A B e W)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_left_path C S A B
          (@computational_cokernel_object C S A B e W) e)));

symbol preabelian_preadditive
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  : τ (@PreadditiveCategory C)
≔ @additive_preadditive C Prod t (@preabelian_additive C Prod t P);

symbol preabelian_kernel
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalKernel C (@preabelian_preadditive C Prod t P) A B f)
≔ (@preabelian_kernels C Prod t P) A B f;

symbol preabelian_cokernel
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalCokernel C (@preabelian_preadditive C Prod t P) A B f)
≔ (@preabelian_cokernels C Prod t P) A B f;

// Coim(f) = Coker(Ker(f)).
symbol computational_coimage
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalCokernel C
      (@preabelian_preadditive C Prod t P)
      (@computational_kernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f))
      A
      (@computational_kernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f)))
≔ (@preabelian_cokernels C Prod t P)
    (@computational_kernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f));

// Im(f) = Ker(Coker(f)).
symbol computational_image
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalKernel C
      (@preabelian_preadditive C Prod t P)
      B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
≔ (@preabelian_kernels C Prod t P)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f));

symbol computational_coimage_object
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@preabelian_preadditive C Prod t P)
    (@computational_kernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    (@computational_coimage C Prod t P A B f);

symbol computational_coimage_projection
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C A (@computational_coimage_object C Prod t P A B f))
≔ @computational_cokernel_morphism C
    (@preabelian_preadditive C Prod t P)
    (@computational_kernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    (@computational_coimage C Prod t P A B f);

// Selected coimage projection annihilates the selected kernel embedding.
symbol computational_coimage_annihilation
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_kernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f))
      (@computational_coimage_object C Prod t P A B f))
      (@comp_fapp0 C _ _ _
        (@computational_coimage_projection C Prod t P A B f)
        (@computational_kernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_kernel C Prod t P A B f)))
      (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
        (@computational_kernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_kernel C Prod t P A B f))
        (@computational_coimage_object C Prod t P A B f)))
≔ @computational_cokernel_annihilation C
    (@preabelian_preadditive C Prod t P)
    (@computational_kernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    (@computational_coimage C Prod t P A B f);

// The coimage projection annihilates every arrow annihilated by f.
symbol computational_coimage_annihilates_cone
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C
    (@preabelian_preadditive C Prod t P) A B f T))
  : τ (@= (Hom C T (@computational_coimage_object C Prod t P A B f))
      (@comp_fapp0 C _ _ _
        (@computational_coimage_projection C Prod t P A B f)
        (@weak_kernel_annihilator_arrow C
          (@preabelian_preadditive C Prod t P) A B f T cone))
      (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P) T
        (@computational_coimage_object C Prod t P A B f)))
≔ @eq_trans _ _ _ _
    (@eq_ap (Hom C T A)
      (Hom C T (@computational_coimage_object C Prod t P A B f))
      (λ h : τ (Hom C T A),
        @comp_fapp0 C _ _ _
          (@computational_coimage_projection C Prod t P A B f) h)
      _ _
      (@eq_sym _ _ _
        (@computational_kernel_lift_path C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_kernel C Prod t P A B f) T cone)))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@computational_coimage_projection C Prod t P A B f)
        (@computational_kernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_kernel C Prod t P A B f))
        (@computational_kernel_lift C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_kernel C Prod t P A B f) T cone))
      (@preadditive_precompose_zero_path C
        (@preabelian_preadditive C Prod t P) T
        (@computational_kernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_kernel C Prod t P A B f))
        (@computational_coimage_object C Prod t P A B f)
        (@comp_fapp0 C _ _ _
          (@computational_coimage_projection C Prod t P A B f)
          (@computational_kernel_morphism C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_kernel C Prod t P A B f)))
        (@computational_kernel_lift C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_kernel C Prod t P A B f) T cone)
        (@computational_coimage_annihilation C Prod t P A B f)));

symbol computational_image_object
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@preabelian_preadditive C Prod t P)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_image C Prod t P A B f);

symbol computational_image_embedding
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C (@computational_image_object C Prod t P A B f) B)
≔ @computational_kernel_morphism C
    (@preabelian_preadditive C Prod t P)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_image C Prod t P A B f);

// Every arrow coannihilating f also coannihilates the selected image
// embedding. This is the direct dual of coimage annihilation of kernel cones.
symbol computational_image_coannihilates_cocone
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (T : τ (Obj C))
  (cone : τ (@CokernelCoannihilator C
    (@preabelian_preadditive C Prod t P) A B f T))
  : τ (@= (Hom C (@computational_image_object C Prod t P A B f) T)
      (@comp_fapp0 C _ _ _
        (@cokernel_coannihilator_arrow C
          (@preabelian_preadditive C Prod t P) A B f T cone)
        (@computational_image_embedding C Prod t P A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
        (@computational_image_object C Prod t P A B f) T))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@eq_ap
        (Hom C B T)
        (Hom C (@computational_image_object C Prod t P A B f) T)
        (λ h : τ (Hom C B T),
          @comp_fapp0 C _ _ _ h
            (@computational_image_embedding C Prod t P A B f))
        _ _
        (@computational_cokernel_colift_path C
          (@preabelian_preadditive C Prod t P)
          A B f
          (@preabelian_cokernel C Prod t P A B f)
          T cone)))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C _ _ _ _
          (@computational_cokernel_colift C
            (@preabelian_preadditive C Prod t P)
            A B f
            (@preabelian_cokernel C Prod t P A B f)
            T cone)
          (@computational_cokernel_morphism C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          (@computational_image_embedding C Prod t P A B f)))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C (@computational_image_object C Prod t P A B f)
            (@computational_cokernel_object C
              (@preabelian_preadditive C Prod t P) A B f
              (@preabelian_cokernel C Prod t P A B f)))
          (Hom C (@computational_image_object C Prod t P A B f) T)
          (λ h : τ (Hom C
              (@computational_image_object C Prod t P A B f)
              (@computational_cokernel_object C
                (@preabelian_preadditive C Prod t P) A B f
                (@preabelian_cokernel C Prod t P A B f))),
            @comp_fapp0 C _ _ _
              (@computational_cokernel_colift C
                (@preabelian_preadditive C Prod t P)
                A B f
                (@preabelian_cokernel C Prod t P A B f)
                T cone)
              h)
          _ _
          (@computational_kernel_annihilation C
            (@preabelian_preadditive C Prod t P)
            B
            (@computational_cokernel_object C
              (@preabelian_preadditive C Prod t P) A B f
              (@preabelian_cokernel C Prod t P A B f))
            (@computational_cokernel_morphism C
              (@preabelian_preadditive C Prod t P) A B f
              (@preabelian_cokernel C Prod t P A B f))
            (@computational_image C Prod t P A B f)))
        (@preadditive_comp_zero_right_path C
          (@preabelian_preadditive C Prod t P)
          (@computational_image_object C Prod t P A B f)
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          T
            (@computational_cokernel_colift C
              (@preabelian_preadditive C Prod t P)
              A B f
              (@preabelian_cokernel C Prod t P A B f)
              T cone))));

// Every selected factor through Im(f) is killed by every cocone of f.
symbol computational_image_factor_annihilated_by_cocone
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (T : τ (Obj C))
  (cone : τ (@WeakKernelAnnihilator C
    (@preabelian_preadditive C Prod t P)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    T))
  (U : τ (Obj C))
  (cocone : τ (@CokernelCoannihilator C
    (@preabelian_preadditive C Prod t P) A B f U))
  : τ (@= (Hom C T U)
      (@comp_fapp0 C _ _ _
        (@cokernel_coannihilator_arrow C
          (@preabelian_preadditive C Prod t P) A B f U cocone)
        (@weak_kernel_annihilator_arrow C
          (@preabelian_preadditive C Prod t P)
          B
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          (@computational_cokernel_morphism C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          T cone))
      (@preadditive_hom_zero C
        (@preabelian_preadditive C Prod t P) T U))
≔ @kernel_lift_postannihilation_path C
    (@preabelian_preadditive C Prod t P)
    T
    (@computational_image_object C Prod t P A B f)
    B U
    (@computational_image_embedding C Prod t P A B f)
    (@computational_kernel_lift C
      (@preabelian_preadditive C Prod t P)
      B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_image C Prod t P A B f)
      T cone)
    (@weak_kernel_annihilator_arrow C
      (@preabelian_preadditive C Prod t P)
      B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      T cone)
    (@cokernel_coannihilator_arrow C
      (@preabelian_preadditive C Prod t P) A B f U cocone)
    (@computational_kernel_lift_path C
      (@preabelian_preadditive C Prod t P)
      B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_image C Prod t P A B f)
      T cone)
    (@computational_image_coannihilates_cocone C Prod t P A B f U cocone);

// f is coannihilated by its selected kernel.
symbol coimage_to_target_cone
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@CokernelCoannihilator C
      (@preabelian_preadditive C Prod t P)
      (@computational_kernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f))
      A
      (@computational_kernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f))
      B)
≔ @Struct_sigma
    (Hom C A B)
    (λ h : τ (Hom C A B),
      @= (Hom C
          (@computational_kernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_kernel C Prod t P A B f)) B)
        (@comp_fapp0 C
          (@computational_kernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_kernel C Prod t P A B f)) A B h
          (@computational_kernel_morphism C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_kernel C Prod t P A B f)))
        (@preadditive_hom_zero C
          (@preabelian_preadditive C Prod t P)
          (@computational_kernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_kernel C Prod t P A B f)) B))
    f
    (@computational_kernel_annihilation C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f));

// Coimage coastriction bar_f : Coim(f) -> B.
symbol coimage_to_target
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C (@computational_coimage_object C Prod t P A B f) B)
≔ @computational_cokernel_colift C
    (@preabelian_preadditive C Prod t P)
    (@computational_kernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    (@computational_coimage C Prod t P A B f)
    B (@coimage_to_target_cone C Prod t P A B f);

symbol coimage_to_target_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C A B)
      (@comp_fapp0 C A
        (@computational_coimage_object C Prod t P A B f) B
        (@coimage_to_target C Prod t P A B f)
        (@computational_coimage_projection C Prod t P A B f))
      f)
≔ @computational_cokernel_colift_path C
    (@preabelian_preadditive C Prod t P)
    (@computational_kernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_kernel C Prod t P A B f))
    (@computational_coimage C Prod t P A B f)
    B (@coimage_to_target_cone C Prod t P A B f);

symbol coimage_to_target_cokernel_congr_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C A
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
      (@comp_fapp0 C A B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@comp_fapp0 C A
          (@computational_coimage_object C Prod t P A B f) B
          (@coimage_to_target C Prod t P A B f)
          (@computational_coimage_projection C Prod t P A B f)))
      (@comp_fapp0 C A B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f)) f))
≔ @eq_ap
    (Hom C A B)
    (Hom C A
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
    (λ z : τ (Hom C A B),
      @comp_fapp0 C A B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f)) z)
    (@comp_fapp0 C A
      (@computational_coimage_object C Prod t P A B f) B
      (@coimage_to_target C Prod t P A B f)
      (@computational_coimage_projection C Prod t P A B f))
    f
    (@coimage_to_target_path C Prod t P A B f);

symbol coimage_to_target_cokernel_zero_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C A
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
      (@comp_fapp0 C A B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@comp_fapp0 C A
          (@computational_coimage_object C Prod t P A B f) B
          (@coimage_to_target C Prod t P A B f)
          (@computational_coimage_projection C Prod t P A B f)))
      (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P) A
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))))
≔ @eq_trans
    (Hom C A
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
    (@comp_fapp0 C A B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@comp_fapp0 C A
        (@computational_coimage_object C Prod t P A B f) B
        (@coimage_to_target C Prod t P A B f)
        (@computational_coimage_projection C Prod t P A B f)))
    (@comp_fapp0 C A B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)) f)
    (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P) A
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
    (@coimage_to_target_cokernel_congr_path C Prod t P A B f)
    (@computational_cokernel_annihilation C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f));

// After precomposition with the epic coimage projection, q_f o bar_f is zero.
symbol coimage_image_annihilation_after_projection_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C A
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
      (@comp_fapp0 C A
        (@computational_coimage_object C Prod t P A B f)
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@comp_fapp0 C
          (@computational_coimage_object C Prod t P A B f) B
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          (@computational_cokernel_morphism C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          (@coimage_to_target C Prod t P A B f))
        (@computational_coimage_projection C Prod t P A B f))
      (@comp_fapp0 C A
        (@computational_coimage_object C Prod t P A B f)
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
          (@computational_coimage_object C Prod t P A B f)
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f)))
        (@computational_coimage_projection C Prod t P A B f)))
≔ @eq_trans
    (Hom C A
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
    (@comp_fapp0 C A
      (@computational_coimage_object C Prod t P A B f)
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@comp_fapp0 C
        (@computational_coimage_object C Prod t P A B f) B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@coimage_to_target C Prod t P A B f))
      (@computational_coimage_projection C Prod t P A B f))
    (@comp_fapp0 C A B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@comp_fapp0 C A
        (@computational_coimage_object C Prod t P A B f) B
        (@coimage_to_target C Prod t P A B f)
        (@computational_coimage_projection C Prod t P A B f)))
    (@comp_fapp0 C A
      (@computational_coimage_object C Prod t P A B f)
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
        (@computational_coimage_object C Prod t P A B f)
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f)))
      (@computational_coimage_projection C Prod t P A B f))
    (@eq_sym _ _ _
      (@comp_assoc C A
        (@computational_coimage_object C Prod t P A B f) B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@coimage_to_target C Prod t P A B f)
        (@computational_coimage_projection C Prod t P A B f)))
    (@eq_trans
      (Hom C A
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f)))
      (@comp_fapp0 C A B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@comp_fapp0 C A
          (@computational_coimage_object C Prod t P A B f) B
          (@coimage_to_target C Prod t P A B f)
          (@computational_coimage_projection C Prod t P A B f)))
      (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P) A
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f)))
      (@comp_fapp0 C A
        (@computational_coimage_object C Prod t P A B f)
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
          (@computational_coimage_object C Prod t P A B f)
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f)))
        (@computational_coimage_projection C Prod t P A B f))
      (@coimage_to_target_cokernel_zero_path C Prod t P A B f)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_left_path C
          (@preabelian_preadditive C Prod t P) A
          (@computational_coimage_object C Prod t P A B f)
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          (@computational_coimage_projection C Prod t P A B f))));

symbol coimage_to_target_image_annihilation_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_coimage_object C Prod t P A B f)
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
      (@comp_fapp0 C
        (@computational_coimage_object C Prod t P A B f) B
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))
        (@coimage_to_target C Prod t P A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
        (@computational_coimage_object C Prod t P A B f)
        (@computational_cokernel_object C
          (@preabelian_preadditive C Prod t P) A B f
          (@preabelian_cokernel C Prod t P A B f))))
≔ (@computational_cokernel_morphism_is_epic C
      (@preabelian_preadditive C Prod t P)
      (@computational_kernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f))
      A
      (@computational_kernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f))
      (@computational_coimage C Prod t P A B f))
    (@computational_cokernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@comp_fapp0 C
      (@computational_coimage_object C Prod t P A B f) B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@coimage_to_target C Prod t P A B f))
    (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
      (@computational_coimage_object C Prod t P A B f)
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)))
    (@coimage_image_annihilation_after_projection_path C Prod t P A B f);

symbol coimage_to_image_cone
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@WeakKernelAnnihilator C
      (@preabelian_preadditive C Prod t P)
      B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_coimage_object C Prod t P A B f))
≔ @Struct_sigma
    (Hom C (@computational_coimage_object C Prod t P A B f) B)
    (λ h : τ (Hom C (@computational_coimage_object C Prod t P A B f) B),
      @= (Hom C
          (@computational_coimage_object C Prod t P A B f)
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f)))
        (@comp_fapp0 C
          (@computational_coimage_object C Prod t P A B f) B
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))
          (@computational_cokernel_morphism C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f)) h)
        (@preadditive_hom_zero C (@preabelian_preadditive C Prod t P)
          (@computational_coimage_object C Prod t P A B f)
          (@computational_cokernel_object C
            (@preabelian_preadditive C Prod t P) A B f
            (@preabelian_cokernel C Prod t P A B f))))
    (@coimage_to_target C Prod t P A B f)
    (@coimage_to_target_image_annihilation_path C Prod t P A B f);

symbol coimage_image_comparison
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C
      (@computational_coimage_object C Prod t P A B f)
      (@computational_image_object C Prod t P A B f))
≔ @computational_kernel_lift C
    (@preabelian_preadditive C Prod t P)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_image C Prod t P A B f)
    (@computational_coimage_object C Prod t P A B f)
    (@coimage_to_image_cone C Prod t P A B f);

symbol coimage_image_comparison_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C (@computational_coimage_object C Prod t P A B f) B)
      (@comp_fapp0 C
        (@computational_coimage_object C Prod t P A B f)
        (@computational_image_object C Prod t P A B f) B
        (@computational_image_embedding C Prod t P A B f)
        (@coimage_image_comparison C Prod t P A B f))
      (@coimage_to_target C Prod t P A B f))
≔ @computational_kernel_lift_path C
    (@preabelian_preadditive C Prod t P)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C Prod t P) A B f
      (@preabelian_cokernel C Prod t P A B f))
    (@computational_image C Prod t P A B f)
    (@computational_coimage_object C Prod t P A B f)
    (@coimage_to_image_cone C Prod t P A B f);

symbol coimage_image_factorization_path
  [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (P : τ (@PreAbelianCategory C Prod t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C A B)
      (@comp_fapp0 C A
        (@computational_image_object C Prod t P A B f) B
        (@computational_image_embedding C Prod t P A B f)
        (@comp_fapp0 C A
          (@computational_coimage_object C Prod t P A B f)
          (@computational_image_object C Prod t P A B f)
          (@coimage_image_comparison C Prod t P A B f)
          (@computational_coimage_projection C Prod t P A B f)))
      f)
≔ @eq_trans
    (Hom C A B)
    _
    (@comp_fapp0 C A
      (@computational_coimage_object C Prod t P A B f) B
      (@comp_fapp0 C
        (@computational_coimage_object C Prod t P A B f)
        (@computational_image_object C Prod t P A B f) B
        (@computational_image_embedding C Prod t P A B f)
        (@coimage_image_comparison C Prod t P A B f))
      (@computational_coimage_projection C Prod t P A B f))
    f
    (@comp_assoc C A
      (@computational_coimage_object C Prod t P A B f)
      (@computational_image_object C Prod t P A B f) B
      (@computational_image_embedding C Prod t P A B f)
      (@coimage_image_comparison C Prod t P A B f)
      (@computational_coimage_projection C Prod t P A B f))
    (@eq_trans
      (Hom C A B)
      _
      (@comp_fapp0 C A
        (@computational_coimage_object C Prod t P A B f) B
        (@coimage_to_target C Prod t P A B f)
        (@computational_coimage_projection C Prod t P A B f))
      f
      (@eq_ap
        (Hom C (@computational_coimage_object C Prod t P A B f) B)
        (Hom C A B)
        (λ z : τ (Hom C
            (@computational_coimage_object C Prod t P A B f) B),
          @comp_fapp0 C A
            (@computational_coimage_object C Prod t P A B f) B z
            (@computational_coimage_projection C Prod t P A B f))
        _ _ (@coimage_image_comparison_path C Prod t P A B f))
      (@coimage_to_target_path C Prod t P A B f));
