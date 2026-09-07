/* A monomorphism is canonically isomorphic to its selected image. */

require open emdash.emdash3_2_mono_epi_comparisons;
require open emdash.emdash3_2_abelian_images;

symbol monic_image_factor_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@WeakKernelAnnihilator C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f)) A)
≔ @Struct_sigma (Hom C A B)
    (λ h : τ (Hom C A B), @= (Hom C A (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)))
      (@comp_fapp0 C _ _ _ (@computational_cokernel_morphism C (@additive_preadditive C P t
        (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f)) h)
      (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A
        (@computational_cokernel_object C (@additive_preadditive C P t
        (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))))
    f (@computational_cokernel_annihilation C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f));

symbol monic_image_comparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C A (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)))
≔ @computational_kernel_lift C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
  (@computational_cokernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_cokernel_morphism C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_image C P t PA A B f) A
    (@monic_image_factor_cone C P t PA A B f);

symbol monic_image_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C A B) (@comp_fapp0 C _ _ _ (@computational_kernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) (@monic_image_comparison C P t PA A B f)) f)
≔ @computational_kernel_lift_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
  (@computational_cokernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_cokernel_morphism C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_image C P t PA A B f) A
    (@monic_image_factor_cone C P t PA A B f);

symbol monic_image_inverse_test
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@NormalMonoTest C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f) (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)))
≔ @Struct_sigma (Hom C (@computational_kernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) B (@computational_cokernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_cokernel_morphism C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_image C P t PA A B f)) B)
    (λ h : τ (Hom C (@computational_kernel_object C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)) B), @= (Hom C
      (@computational_kernel_object C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
      (@computational_cokernel_object C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f)))
      (@comp_fapp0 C _ _ _ (@computational_cokernel_morphism C (@additive_preadditive C P t
        (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f)) h)
      (@preadditive_hom_zero C (@additive_preadditive C P t (@preabelian_additive C P t PA))
        (@computational_kernel_object C (@additive_preadditive C P t
        (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
        (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
        (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
        (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
        (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
        (@computational_cokernel_object C (@additive_preadditive C P t
        (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))))
    (@computational_kernel_morphism C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
      (@computational_kernel_annihilation C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f));

symbol monic_image_inverse
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  : τ (Hom C (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)) A)
≔ @lift_along_monomorphism C (@additive_preadditive C P t (@preabelian_additive C P t PA))
    (@preabelian_cokernels C P t PA)
    normal
    A B f monic (@computational_kernel_object C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
      (@monic_image_inverse_test C P t PA A B f);

symbol monic_image_inverse_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  : τ (@= (Hom C (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)) B)
    (@comp_fapp0 C _ _ _ f (@monic_image_inverse C P t PA A B f normal monic))
    (@computational_kernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)))
≔ @lift_along_monomorphism_path C (@additive_preadditive C P t (@preabelian_additive C P t PA))
    (@preabelian_cokernels C P t PA)
    normal
    A B f monic (@computational_kernel_object C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
      (@monic_image_inverse_test C P t PA A B f);

symbol monic_image_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  : τ (@IsoEvidence C A (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)))
≔ @iso_from_monic_comparisons C A (@computational_kernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) B (@computational_cokernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_cokernel_morphism C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_image C P t PA A B f)) B
    f (@computational_kernel_morphism C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
      (@monic_image_comparison C P t PA A B f)
      (@monic_image_inverse C P t PA A B f normal monic) monic
    (@computational_kernel_morphism_is_monic C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
    (@monic_image_comparison_path C P t PA A B f)
    (@monic_image_inverse_path C P t PA A B f normal monic);
