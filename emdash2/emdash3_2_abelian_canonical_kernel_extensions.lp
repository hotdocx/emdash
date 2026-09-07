/* Canonical kernel rows expose the monomorphic local-extension criterion. */

require open emdash.emdash3_2_abelian_canonical_kernel_extensions_foundation;

symbol abelian_canonical_kernel_extension_pushout
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
  : τ (@ComputationalPushout C P t
      (@preabelian_additive C P t PA)
      B
      (@computational_coimage_object C P t PA A B f)
      T
      (@coimage_to_target C P t PA A B f)
      (@abelian_canonical_kernel_extension_colift C P t PA A B T f cocone))
≔ @abelian_selected_pushout C P t
    (@image_bimorphism_abelian C P t PA M E)
    (@computational_coimage_object C P t PA A B f)
    B T
    (@coimage_to_target C P t PA A B f)
    (@abelian_canonical_kernel_extension_colift C P t PA A B T f cocone);

symbol abelian_canonical_kernel_extension_object
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
  : τ (Obj C)
≔ @computational_pushout_object C P t
    (@preabelian_additive C P t PA)
    B
    (@computational_coimage_object C P t PA A B f)
    T
    (@coimage_to_target C P t PA A B f)
    (@abelian_canonical_kernel_extension_colift C P t PA A B T f cocone)
    (@abelian_canonical_kernel_extension_pushout C P t
      PA M E A B T f cocone);

symbol abelian_canonical_kernel_extension_monomorphism
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
  : τ (Hom C T
      (@abelian_canonical_kernel_extension_object C P t
        PA M E A B T f cocone))
≔ @computational_pushout_inj2 C P t
    (@preabelian_additive C P t PA)
    B
    (@computational_coimage_object C P t PA A B f)
    T
    (@coimage_to_target C P t PA A B f)
    (@abelian_canonical_kernel_extension_colift C P t PA A B T f cocone)
    (@abelian_canonical_kernel_extension_pushout C P t
      PA M E A B T f cocone);

symbol abelian_canonical_kernel_extension_is_monic
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
  : τ (@IsMonic C T
      (@abelian_canonical_kernel_extension_object C P t
        PA M E A B T f cocone)
      (@abelian_canonical_kernel_extension_monomorphism C P t
        PA M E A B T f cocone))
≔ @abelian_pushout_monic_injection C P t
    (@image_bimorphism_abelian C P t PA M E)
    (@computational_coimage_object C P t PA A B f)
    B T
    (@coimage_to_target C P t PA A B f)
    (@abelian_canonical_kernel_extension_colift C P t PA A B T f cocone)
    (@abelian_canonical_kernel_target_monic C P t PA M E A B f);

symbol abelian_canonical_kernel_extension_factor
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
  : τ (Hom C B
      (@abelian_canonical_kernel_extension_object C P t
        PA M E A B T f cocone))
≔ @computational_pushout_inj1 C P t
    (@preabelian_additive C P t PA)
    B
    (@computational_coimage_object C P t PA A B f)
    T
    (@coimage_to_target C P t PA A B f)
    (@abelian_canonical_kernel_extension_colift C P t PA A B T f cocone)
    (@abelian_canonical_kernel_extension_pushout C P t
      PA M E A B T f cocone);

symbol abelian_canonical_kernel_extension_path
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
  : τ (@= (Hom C A
      (@abelian_canonical_kernel_extension_object C P t
        PA M E A B T f cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_canonical_kernel_extension_monomorphism C P t
          PA M E A B T f cocone)
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
      (@comp_fapp0 C _ _ _
        (@abelian_canonical_kernel_extension_factor C P t
          PA M E A B T f cocone)
        f))
≔ @eq_trans _ _ _ _
    (@eq_ap
      (Hom C A T)
      (Hom C A
        (@abelian_canonical_kernel_extension_object C P t
          PA M E A B T f cocone))
      (λ h : τ (Hom C A T),
        @comp_fapp0 C _ _ _
          (@abelian_canonical_kernel_extension_monomorphism C P t
            PA M E A B T f cocone) h)
      _ _
      (@eq_sym _ _ _
        (@abelian_canonical_kernel_extension_colift_path C P t
          PA A B T f cocone)))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_canonical_kernel_extension_monomorphism C P t
          PA M E A B T f cocone)
        (@abelian_canonical_kernel_extension_colift C P t
          PA A B T f cocone)
        (@computational_coimage_projection C P t PA A B f))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@computational_coimage_object C P t PA A B f)
            (@abelian_canonical_kernel_extension_object C P t
              PA M E A B T f cocone))
          (Hom C A
            (@abelian_canonical_kernel_extension_object C P t
              PA M E A B T f cocone))
          (λ h : τ (Hom C
              (@computational_coimage_object C P t PA A B f)
              (@abelian_canonical_kernel_extension_object C P t
                PA M E A B T f cocone)),
            @comp_fapp0 C _ _ _ h
              (@computational_coimage_projection C P t PA A B f))
          _ _
          (@eq_sym _ _ _
            (@computational_pushout_compatibility_path C P t
              (@preabelian_additive C P t PA)
              B
              (@computational_coimage_object C P t PA A B f)
              T
              (@coimage_to_target C P t PA A B f)
              (@abelian_canonical_kernel_extension_colift C P t
                PA A B T f cocone)
              (@abelian_canonical_kernel_extension_pushout C P t
                PA M E A B T f cocone))))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_canonical_kernel_extension_factor C P t
                PA M E A B T f cocone)
              (@coimage_to_target C P t PA A B f)
              (@computational_coimage_projection C P t PA A B f)))
          (@eq_ap
            (Hom C A B)
            (Hom C A
              (@abelian_canonical_kernel_extension_object C P t
                PA M E A B T f cocone))
            (λ h : τ (Hom C A B),
              @comp_fapp0 C _ _ _
                (@abelian_canonical_kernel_extension_factor C P t
                  PA M E A B T f cocone) h)
            _ _
            (@coimage_to_target_path C P t PA A B f)))));

symbol abelian_canonical_kernel_extension
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
  : τ (@ComputationalExactExtensionWitness C P t PA
      (@computational_kernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_kernel C P t PA A B f))
      A B
      (@abelian_canonical_kernel_pair_explicit C P t PA A B f)
      T cocone)
≔ @computational_exact_extension_intro C P t PA
    (@computational_kernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_kernel C P t PA A B f))
    A B
    (@abelian_canonical_kernel_pair_explicit C P t PA A B f)
    T cocone
    (@abelian_canonical_kernel_extension_object C P t
      PA M E A B T f cocone)
    (@abelian_canonical_kernel_extension_monomorphism C P t
      PA M E A B T f cocone)
    (@abelian_canonical_kernel_extension_is_monic C P t
      PA M E A B T f cocone)
    (@abelian_canonical_kernel_extension_factor C P t
      PA M E A B T f cocone)
    (@abelian_canonical_kernel_extension_path C P t
      PA M E A B T f cocone);

symbol abelian_canonical_kernel_extensions
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
  : τ (@HasComputationalExactExtensions C P t PA
      (@computational_kernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_kernel C P t PA A B f))
      A B
      (@abelian_canonical_kernel_pair_explicit C P t PA A B f))
≔ λ T : τ (Obj C),
   λ cocone : τ (@CokernelCoannihilator C
      (@preabelian_preadditive C P t PA)
      (@computational_kernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_kernel C P t PA A B f))
      A
      (@computational_kernel_morphism C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_kernel C P t PA A B f))
      T),
     @abelian_canonical_kernel_extension C P t
       PA M E A B T f cocone;
