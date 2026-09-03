/* Canonical image factor point in one explicit pre-Abelian fibre. */

require open emdash.emdash3_2_abelian_canonical_cokernel_foundation;

symbol AbelianCanonicalCokernelFactorSpace_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : Grpd
≔ @KernelFactorSpace C
    (@preabelian_preadditive C P t PA)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@computational_image_object C P t PA A B f)
    (@computational_image_embedding C P t PA A B f)
    A
    (@abelian_canonical_cokernel_image_cone_explicit C P t PA A B f);

symbol abelian_canonical_cokernel_candidate_point_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@AbelianCanonicalCokernelFactorSpace_explicit C P t PA A B f)
≔ @Struct_sigma
    (Hom C A (@computational_image_object C P t PA A B f))
    (λ h : τ (Hom C A (@computational_image_object C P t PA A B f)),
      @= (Hom C A B)
        (@comp_fapp0 C _ _ _
          (@computational_image_embedding C P t PA A B f) h)
        f)
    (@abelian_canonical_cokernel_candidate_explicit C P t PA A B f)
    (@coimage_image_factorization_path C P t PA A B f);

symbol abelian_canonical_cokernel_factor_contr_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (IsContr
      (@AbelianCanonicalCokernelFactorSpace_explicit C P t PA A B f))
≔ @computational_kernel_factor_contr C
    (@preabelian_preadditive C P t PA)
    B
    (@computational_cokernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)
    A
    (@abelian_canonical_cokernel_image_cone_explicit C P t PA A B f);
