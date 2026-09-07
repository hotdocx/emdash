/* The selected image row reuses its existing whole image kernel. */

require open emdash.emdash3_2_kernel_short_exact_rows;
require open emdash.emdash3_2_abelian_images;

symbol selected_short_exact_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA))
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)))
≔ @kernel_short_exact_pair C P t PA B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
  (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
  (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f);

symbol selected_short_exact_evidence
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalShortExactTriple C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f))
      (@selected_short_exact_pair C P t PA A B f))
≔ @kernel_short_exact_evidence C P t PA B (@computational_cokernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
  (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
  (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f)
    (@computational_cokernel_morphism_is_epic C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f));

symbol selected_short_exact_row
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalShortExactRow C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)))
≔ @kernel_short_exact_row C P t PA B (@computational_cokernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_cokernel_morphism C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
  (@computational_image C P t PA A B f)
    (@computational_cokernel_morphism_is_epic C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f));
