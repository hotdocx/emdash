/* Canonical kernel-row coimage factors for exact extensions. */

require open emdash.emdash3_2_exactness_extensions_foundation;
require open emdash.emdash3_2_abelian_image_bimorphisms;

symbol abelian_canonical_kernel_pair_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalChainPair C
      (@preabelian_preadditive C P t PA)
      (@computational_kernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_kernel C P t PA A B f))
      A B)
≔ @computational_chain_pair_intro C
    (@preabelian_preadditive C P t PA)
    (@computational_kernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    A B
    (@computational_kernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    f
    (@computational_kernel_annihilation C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f));

symbol abelian_canonical_kernel_extension_colift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B T : τ (Obj C)]
  (f : τ (Hom C A B))
  (cocone : τ (@CokernelCoannihilator C
    (@preabelian_preadditive C P t PA)
    (@computational_kernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    T))
  : τ (Hom C (@computational_coimage_object C P t PA A B f) T)
≔ @computational_cokernel_colift C
    (@preabelian_preadditive C P t PA)
    (@computational_kernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    (@computational_coimage C P t PA A B f)
    T cocone;

symbol abelian_canonical_kernel_extension_colift_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B T : τ (Obj C)]
  (f : τ (Hom C A B))
  (cocone : τ (@CokernelCoannihilator C
    (@preabelian_preadditive C P t PA)
    (@computational_kernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    T))
  : τ (@= (Hom C A T)
      (@comp_fapp0 C _ _ _
        (@abelian_canonical_kernel_extension_colift C P t PA A B T f cocone)
        (@computational_coimage_projection C P t PA A B f))
      (@cokernel_coannihilator_arrow C
        (@preabelian_preadditive C P t PA)
        (@computational_kernel_object C
          (@preabelian_preadditive C P t PA) A B f
          (@preabelian_kernel C P t PA A B f))
        A
        (@computational_kernel_morphism C
          (@preabelian_preadditive C P t PA) A B f
          (@preabelian_kernel C P t PA A B f))
        T cocone))
≔ @computational_cokernel_colift_path C
    (@preabelian_preadditive C P t PA)
    (@computational_kernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    A
    (@computational_kernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    (@computational_coimage C P t PA A B f)
    T cocone;

symbol abelian_canonical_kernel_target_monic
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
      B
      (@coimage_to_target C P t PA A B f))
≔ @is_monic_of_equal C
    (@computational_coimage_object C P t PA A B f)
    B
    (@coimage_to_target C P t PA A B f)
    (@comp_fapp0 C _ _ _
      (@computational_image_embedding C P t PA A B f)
      (@coimage_image_comparison C P t PA A B f))
    (@eq_sym _ _ _ (@coimage_image_comparison_path C P t PA A B f))
    (@is_monic_comp C
      (@computational_coimage_object C P t PA A B f)
      (@computational_image_object C P t PA A B f)
      B
      (@coimage_image_comparison C P t PA A B f)
      (@computational_image_embedding C P t PA A B f)
      (@coimage_image_comparison_is_monic C P t PA M E A B f)
      (@computational_kernel_morphism_is_monic C
        (@preabelian_preadditive C P t PA)
        B
        (@computational_cokernel_object C
          (@preabelian_preadditive C P t PA) A B f
          (@preabelian_cokernel C P t PA A B f))
        (@computational_cokernel_morphism C
          (@preabelian_preadditive C P t PA) A B f
          (@preabelian_cokernel C P t PA A B f))
        (@computational_image C P t PA A B f)));
