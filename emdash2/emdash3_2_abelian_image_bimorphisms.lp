/*
  Constructive bimorphism of the canonical coimage-to-image comparison.

  Image and coimage terms use one literal PreAbelianCategory parameter. The
  implementation keeps its normality capabilities visible so that the
  ComputationalAbelianCategory constructor reduces immediately at the two
  stability theorems. Public wrappers recover the ordinary one-capability
  interface. No comparison property, inverse, or equality is postulated.
*/

require open emdash.emdash3_2_preabelian_bimorphism_lemmas;
require open emdash.emdash3_2_abelian_images;

symbol image_bimorphism_abelian
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  : τ (@ComputationalAbelianCategory C P t)
≔ @computational_abelian_category_intro C P t PA M E;

symbol image_bimorphism_comparison_kernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalKernel C
      (@preabelian_preadditive C P t PA)
      (@computational_coimage_object C P t PA A B f)
      (@computational_image_object C P t PA A B f)
      (@coimage_image_comparison C P t PA A B f))
≔ (@preabelian_kernels C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f);

symbol image_bimorphism_comparison_kernel_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_kernel C P t PA A B f);

symbol image_bimorphism_comparison_kernel_embedding
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C
      (@image_bimorphism_comparison_kernel_object C P t PA A B f)
      (@computational_coimage_object C P t PA A B f))
≔ @computational_kernel_morphism C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_kernel C P t PA A B f);

symbol image_bimorphism_comparison_kernel_annihilation
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@image_bimorphism_comparison_kernel_object C P t PA A B f)
      (@computational_image_object C P t PA A B f))
      (@comp_fapp0 C _ _ _
        (@coimage_image_comparison C P t PA A B f)
        (@image_bimorphism_comparison_kernel_embedding C P t PA A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@image_bimorphism_comparison_kernel_object C P t PA A B f)
        (@computational_image_object C P t PA A B f)))
≔ @computational_kernel_annihilation C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_kernel C P t PA A B f);

symbol image_bimorphism_coimage_projection_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsEpic C A
      (@computational_coimage_object C P t PA A B f)
      (@computational_coimage_projection C P t PA A B f))
≔ @computational_cokernel_morphism_is_epic C
    (@preabelian_preadditive C P t PA)
    (@computational_kernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    (@computational_coimage C P t PA A B f);

symbol image_bimorphism_kernel_pullback
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalFiberProduct C P t
      (@preabelian_additive C P t PA)
      (@image_bimorphism_comparison_kernel_object C P t PA A B f)
      (@computational_coimage_object C P t PA A B f)
      A
      (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
      (@computational_coimage_projection C P t PA A B f))
≔ @abelian_selected_fiber_product C P t
    (@image_bimorphism_abelian C P t PA M E)
    (@image_bimorphism_comparison_kernel_object C P t PA A B f)
    (@computational_coimage_object C P t PA A B f)
    A
    (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f);

symbol image_bimorphism_kernel_pullback_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Obj C)
≔ @computational_fiber_product_object C P t
    (@preabelian_additive C P t PA)
    (@image_bimorphism_comparison_kernel_object C P t PA A B f)
    (@computational_coimage_object C P t PA A B f)
    A
    (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@image_bimorphism_kernel_pullback C P t PA M E A B f);

symbol image_bimorphism_kernel_pullback_left
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
      (@image_bimorphism_comparison_kernel_object C P t PA A B f))
≔ @computational_fiber_product_proj1 C P t
    (@preabelian_additive C P t PA)
    (@image_bimorphism_comparison_kernel_object C P t PA A B f)
    (@computational_coimage_object C P t PA A B f)
    A
    (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@image_bimorphism_kernel_pullback C P t PA M E A B f);

symbol image_bimorphism_kernel_pullback_right
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f) A)
≔ @computational_fiber_product_proj2 C P t
    (@preabelian_additive C P t PA)
    (@image_bimorphism_comparison_kernel_object C P t PA A B f)
    (@computational_coimage_object C P t PA A B f)
    A
    (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@image_bimorphism_kernel_pullback C P t PA M E A B f);

symbol image_bimorphism_kernel_pullback_left_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsEpic C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
      (@image_bimorphism_comparison_kernel_object C P t PA A B f)
      (@image_bimorphism_kernel_pullback_left C P t PA M E A B f))
≔ @abelian_fiber_product_epic_projection C P t
    (@image_bimorphism_abelian C P t PA M E)
    (@image_bimorphism_comparison_kernel_object C P t PA A B f)
    (@computational_coimage_object C P t PA A B f)
    A
    (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@image_bimorphism_coimage_projection_epic C P t PA A B f);

symbol image_bimorphism_pullback_chi_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
      (@computational_image_object C P t PA A B f))
      (@comp_fapp0 C _ _ _
        (@coimage_image_comparison C P t PA A B f)
        (@comp_fapp0 C _ _ _
          (@computational_coimage_projection C P t PA A B f)
          (@image_bimorphism_kernel_pullback_right C P t PA M E A B f)))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
        (@computational_image_object C P t PA A B f)))
≔ @fiber_product_right_annihilation_path C P t
    (@preabelian_additive C P t PA)
    (@image_bimorphism_comparison_kernel_object C P t PA A B f)
    (@computational_coimage_object C P t PA A B f)
    A
    (@computational_image_object C P t PA A B f)
    (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@image_bimorphism_kernel_pullback C P t PA M E A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_kernel_annihilation C P t PA A B f);

symbol image_bimorphism_pullback_right_f_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f) B)
      (@comp_fapp0 C _ _ _ f
        (@image_bimorphism_kernel_pullback_right C P t PA M E A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@image_bimorphism_kernel_pullback_object C P t PA M E A B f) B))
≔ @preadditive_factorization_right_annihilation_path C
    (@preabelian_preadditive C P t PA)
    (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
    A
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    B
    (@image_bimorphism_kernel_pullback_right C P t PA M E A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    f
    (@coimage_image_factorization_path C P t PA A B f)
    (@image_bimorphism_pullback_chi_zero_path C P t PA M E A B f);

symbol image_bimorphism_pullback_right_kernel_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@WeakKernelAnnihilator C (@preabelian_preadditive C P t PA)
      A B f
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f))
≔ @Struct_sigma
    (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f) A)
    (λ h : τ (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f) A),
      @= (Hom C
        (@image_bimorphism_kernel_pullback_object C P t PA M E A B f) B)
        (@comp_fapp0 C _ _ _ f h)
        (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
          (@image_bimorphism_kernel_pullback_object C P t PA M E A B f) B))
    (@image_bimorphism_kernel_pullback_right C P t PA M E A B f)
    (@image_bimorphism_pullback_right_f_zero_path C P t PA M E A B f);

symbol image_bimorphism_projection_after_right_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
      (@computational_coimage_object C P t PA A B f))
      (@comp_fapp0 C _ _ _
        (@computational_coimage_projection C P t PA A B f)
        (@image_bimorphism_kernel_pullback_right C P t PA M E A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
        (@computational_coimage_object C P t PA A B f)))
≔ @computational_coimage_annihilates_cone C P t PA A B f
    (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
    (@image_bimorphism_pullback_right_kernel_cone C P t PA M E A B f);

symbol image_bimorphism_kernel_after_left_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
      (@computational_coimage_object C P t PA A B f))
      (@comp_fapp0 C _ _ _
        (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
        (@image_bimorphism_kernel_pullback_left C P t PA M E A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
        (@computational_coimage_object C P t PA A B f)))
≔ @eq_trans _ _ _ _
    (@computational_fiber_product_compatibility_path C P t
      (@preabelian_additive C P t PA)
      (@image_bimorphism_comparison_kernel_object C P t PA A B f)
      (@computational_coimage_object C P t PA A B f)
      A
      (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
      (@computational_coimage_projection C P t PA A B f)
      (@image_bimorphism_kernel_pullback C P t PA M E A B f))
    (@image_bimorphism_projection_after_right_zero_path C P t
      PA M E A B f);

symbol image_bimorphism_comparison_kernel_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@image_bimorphism_comparison_kernel_object C P t PA A B f)
      (@computational_coimage_object C P t PA A B f))
      (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@image_bimorphism_comparison_kernel_object C P t PA A B f)
        (@computational_coimage_object C P t PA A B f)))
≔ (@image_bimorphism_kernel_pullback_left_epic C P t PA M E A B f)
    (@computational_coimage_object C P t PA A B f)
    (@image_bimorphism_comparison_kernel_embedding C P t PA A B f)
    (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
      (@image_bimorphism_comparison_kernel_object C P t PA A B f)
      (@computational_coimage_object C P t PA A B f))
    (@eq_trans _ _ _ _
      (@image_bimorphism_kernel_after_left_zero_path C P t PA M E A B f)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_left_path C
          (@preabelian_preadditive C P t PA)
          (@image_bimorphism_kernel_pullback_object C P t PA M E A B f)
          (@image_bimorphism_comparison_kernel_object C P t PA A B f)
          (@computational_coimage_object C P t PA A B f)
          (@image_bimorphism_kernel_pullback_left C P t PA M E A B f))));

symbol coimage_image_comparison_is_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsMonic C
      (@computational_coimage_object C P t PA A B f)
      (@computational_image_object C P t PA A B f)
      (@coimage_image_comparison C P t PA A B f))
≔ @computational_kernel_zero_to_monic C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_kernel C P t PA A B f)
    (@image_bimorphism_comparison_kernel_zero_path C P t PA M E A B f);

symbol image_bimorphism_comparison_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalCokernel C
      (@preabelian_preadditive C P t PA)
      (@computational_coimage_object C P t PA A B f)
      (@computational_image_object C P t PA A B f)
      (@coimage_image_comparison C P t PA A B f))
≔ (@preabelian_cokernels C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f);

symbol image_bimorphism_comparison_cokernel_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_cokernel C P t PA A B f);

symbol image_bimorphism_comparison_cokernel_projection
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C
      (@computational_image_object C P t PA A B f)
      (@image_bimorphism_comparison_cokernel_object C P t PA A B f))
≔ @computational_cokernel_morphism C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_cokernel C P t PA A B f);

symbol image_bimorphism_comparison_cokernel_annihilation
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_coimage_object C P t PA A B f)
      (@image_bimorphism_comparison_cokernel_object C P t PA A B f))
      (@comp_fapp0 C _ _ _
        (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
        (@coimage_image_comparison C P t PA A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@computational_coimage_object C P t PA A B f)
        (@image_bimorphism_comparison_cokernel_object C P t PA A B f)))
≔ @computational_cokernel_annihilation C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_cokernel C P t PA A B f);

symbol image_bimorphism_image_embedding_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsMonic C
      (@computational_image_object C P t PA A B f) B
      (@computational_image_embedding C P t PA A B f))
≔ @computational_kernel_morphism_is_monic C
    (@preabelian_preadditive C P t PA)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f);

symbol image_bimorphism_cokernel_pushout
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalPushout C P t
      (@preabelian_additive C P t PA)
      B
      (@computational_image_object C P t PA A B f)
      (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
      (@computational_image_embedding C P t PA A B f)
      (@image_bimorphism_comparison_cokernel_projection C P t PA A B f))
≔ @abelian_selected_pushout C P t
    (@image_bimorphism_abelian C P t PA M E)
    (@computational_image_object C P t PA A B f)
    B
    (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_projection C P t PA A B f);

symbol image_bimorphism_cokernel_pushout_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Obj C)
≔ @computational_pushout_object C P t
    (@preabelian_additive C P t PA)
    B
    (@computational_image_object C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
    (@image_bimorphism_cokernel_pushout C P t PA M E A B f);

symbol image_bimorphism_cokernel_pushout_left
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C B
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
≔ @computational_pushout_inj1 C P t
    (@preabelian_additive C P t PA)
    B
    (@computational_image_object C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
    (@image_bimorphism_cokernel_pushout C P t PA M E A B f);

symbol image_bimorphism_cokernel_pushout_right
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C
      (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
≔ @computational_pushout_inj2 C P t
    (@preabelian_additive C P t PA)
    B
    (@computational_image_object C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
    (@image_bimorphism_cokernel_pushout C P t PA M E A B f);

symbol image_bimorphism_cokernel_pushout_right_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsMonic C
      (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)
      (@image_bimorphism_cokernel_pushout_right C P t PA M E A B f))
≔ @abelian_pushout_monic_injection C P t
    (@image_bimorphism_abelian C P t PA M E)
    (@computational_image_object C P t PA A B f)
    B
    (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
    (@image_bimorphism_image_embedding_monic C P t PA A B f);

symbol image_bimorphism_pushout_image_comparison_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_coimage_object C P t PA A B f)
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
      (@comp_fapp0 C _ _ _
        (@image_bimorphism_cokernel_pushout_left C P t PA M E A B f)
        (@comp_fapp0 C _ _ _
          (@computational_image_embedding C P t PA A B f)
          (@coimage_image_comparison C P t PA A B f)))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@computational_coimage_object C P t PA A B f)
        (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)))
≔ @pushout_left_annihilation_path C P t
    (@preabelian_additive C P t PA)
    B
    (@computational_image_object C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
    (@image_bimorphism_cokernel_pushout C P t PA M E A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_annihilation C P t PA A B f);

symbol image_bimorphism_pushout_left_f_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C A
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
      (@comp_fapp0 C _ _ _
        (@image_bimorphism_cokernel_pushout_left C P t PA M E A B f) f)
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA) A
        (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)))
≔ @preadditive_factorization_left_annihilation_path C
    (@preabelian_preadditive C P t PA)
    A
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    B
    (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    f
    (@image_bimorphism_cokernel_pushout_left C P t PA M E A B f)
    (@coimage_image_factorization_path C P t PA A B f)
    (@image_bimorphism_pushout_image_comparison_zero_path C P t
      PA M E A B f);

symbol image_bimorphism_pushout_left_cokernel_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@CokernelCoannihilator C (@preabelian_preadditive C P t PA)
      A B f
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
≔ @Struct_sigma
    (Hom C B
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
    (λ h : τ (Hom C B
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)),
      @= (Hom C A
        (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
        (@comp_fapp0 C _ _ _ h f)
        (@preadditive_hom_zero C (@preabelian_preadditive C P t PA) A
          (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)))
    (@image_bimorphism_cokernel_pushout_left C P t PA M E A B f)
    (@image_bimorphism_pushout_left_f_zero_path C P t PA M E A B f);

symbol image_bimorphism_pushout_left_after_image_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_image_object C P t PA A B f)
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
      (@comp_fapp0 C _ _ _
        (@image_bimorphism_cokernel_pushout_left C P t PA M E A B f)
        (@computational_image_embedding C P t PA A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@computational_image_object C P t PA A B f)
        (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)))
≔ @computational_image_coannihilates_cocone C P t PA A B f
    (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)
    (@image_bimorphism_pushout_left_cokernel_cocone C P t PA M E A B f);

symbol image_bimorphism_pushout_right_after_cokernel_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_image_object C P t PA A B f)
      (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f))
      (@comp_fapp0 C _ _ _
        (@image_bimorphism_cokernel_pushout_right C P t PA M E A B f)
        (@image_bimorphism_comparison_cokernel_projection C P t PA A B f))
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@computational_image_object C P t PA A B f)
        (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@computational_pushout_compatibility_path C P t
        (@preabelian_additive C P t PA)
        B
        (@computational_image_object C P t PA A B f)
        (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
        (@computational_image_embedding C P t PA A B f)
        (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
        (@image_bimorphism_cokernel_pushout C P t PA M E A B f)))
    (@image_bimorphism_pushout_left_after_image_zero_path C P t
      PA M E A B f);

symbol image_bimorphism_comparison_cokernel_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_image_object C P t PA A B f)
      (@image_bimorphism_comparison_cokernel_object C P t PA A B f))
      (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
      (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
        (@computational_image_object C P t PA A B f)
        (@image_bimorphism_comparison_cokernel_object C P t PA A B f)))
≔ (@image_bimorphism_cokernel_pushout_right_monic C P t PA M E A B f)
    (@computational_image_object C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_projection C P t PA A B f)
    (@preadditive_hom_zero C (@preabelian_preadditive C P t PA)
      (@computational_image_object C P t PA A B f)
      (@image_bimorphism_comparison_cokernel_object C P t PA A B f))
    (@eq_trans _ _ _ _
      (@image_bimorphism_pushout_right_after_cokernel_zero_path C P t
        PA M E A B f)
      (@eq_sym _ _ _
        (@preadditive_comp_zero_right_path C
          (@preabelian_preadditive C P t PA)
          (@computational_image_object C P t PA A B f)
          (@image_bimorphism_comparison_cokernel_object C P t PA A B f)
          (@image_bimorphism_cokernel_pushout_object C P t PA M E A B f)
          (@image_bimorphism_cokernel_pushout_right C P t PA M E A B f))));

symbol coimage_image_comparison_is_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C
    (@preabelian_preadditive C P t PA)
    (@preabelian_kernels C P t PA)))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsEpic C
      (@computational_coimage_object C P t PA A B f)
      (@computational_image_object C P t PA A B f)
      (@coimage_image_comparison C P t PA A B f))
≔ @computational_cokernel_zero_to_epic C
    (@preabelian_preadditive C P t PA)
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_comparison_cokernel C P t PA A B f)
    (@image_bimorphism_comparison_cokernel_zero_path C P t PA M E A B f);

// Public one-capability observations. The explicit implementation above keeps
// the constructor visible while checking; these wrappers recover the ordinary
// ComputationalAbelianCategory interface.
symbol abelian_coimage_image_comparison_is_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsMonic C
      (@computational_coimage_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@computational_image_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@coimage_image_comparison C P t
        (@abelian_stability_preabelian C P t Ab) A B f))
≔ @coimage_image_comparison_is_monic C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    A B f;

symbol abelian_coimage_image_comparison_is_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@IsEpic C
      (@computational_coimage_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@computational_image_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@coimage_image_comparison C P t
        (@abelian_stability_preabelian C P t Ab) A B f))
≔ @coimage_image_comparison_is_epic C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    A B f;

symbol AbelianCoimageImageComparisonBimorphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : Grpd
≔ @Product_grpd
    (@IsMonic C
      (@computational_coimage_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@computational_image_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@coimage_image_comparison C P t
        (@abelian_stability_preabelian C P t Ab) A B f))
    (@IsEpic C
      (@computational_coimage_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@computational_image_object C P t
        (@abelian_stability_preabelian C P t Ab) A B f)
      (@coimage_image_comparison C P t
        (@abelian_stability_preabelian C P t Ab) A B f));

symbol abelian_coimage_image_comparison_bimorphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@AbelianCoimageImageComparisonBimorphism C P t Ab A B f)
≔ @Product_pair_grpd _ _
    (@abelian_coimage_image_comparison_is_monic C P t Ab A B f)
    (@abelian_coimage_image_comparison_is_epic C P t Ab A B f);
