/* Source comparison for the selected image row, before specializing PA and f. */

require open emdash.emdash3_2_short_exact_row_comparison_fibres;
require open emdash.emdash3_2_selected_short_exact_rows;
require open emdash.emdash3_2_monic_image_comparison;

symbol monic_selected_row_comparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  (normal : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (monic : τ (@IsMonic C A B f))
  : τ (@ShortExactRowSourceComparison C P t PA A (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) f (@selected_short_exact_row C P t PA A B f))
≔ @Struct_sigma (@IsoEvidence C A (@computational_kernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) B (@computational_cokernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_cokernel_morphism C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_image C P t PA A B f)))
    (λ e : τ (@IsoEvidence C A (@computational_kernel_object C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
      (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f))),
      @= (Hom C A B)
        (@comp_fapp0 C _ _ _ (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) (@computational_kernel_object C
          (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
          (@computational_cokernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
          (@computational_cokernel_morphism C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
          (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
          (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
          (@preabelian_cokernel C P t PA A B f)) (@computational_short_exact_row_pair C P t PA
          (@computational_kernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
          (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
          (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
          (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
          (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)) B
          (@computational_cokernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
          (@selected_short_exact_row C P t PA A B f))) (@iso_evidence_to C A
          (@computational_kernel_object C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
          (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
          (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
          (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
          (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)) e)) f)
    (@monic_image_iso C P t PA A B f normal monic)
    (@monic_image_comparison_path C P t PA A B f);
