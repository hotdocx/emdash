/* The selected image isomorphism retains both computed universal factors. */

require open emdash.emdash3_2_monic_image_comparison;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  ⊢ (@iso_evidence_to C A (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
    (@monic_image_iso C P t PA A B f normal monic))
  ≡ @monic_image_comparison C P t PA A B f;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  ⊢ (@iso_evidence_from C A (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))
    (@monic_image_iso C P t PA A B f normal monic))
  ≡ @monic_image_inverse C P t PA A B f normal monic;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  ⊢ @monic_image_comparison_path C P t PA A B f
  : τ (@= (Hom C A B) (@comp_fapp0 C _ _ _ (@computational_kernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) (@iso_evidence_to C A (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) (@monic_image_iso C P t PA A B f normal monic))) f);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  ⊢ @monic_image_inverse_path C P t PA A B f normal monic
  : τ (@= (Hom C (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)) B)
    (@comp_fapp0 C _ _ _ f (@iso_evidence_from C A (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) (@monic_image_iso C P t PA A B f normal monic)))
    (@computational_kernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)));
