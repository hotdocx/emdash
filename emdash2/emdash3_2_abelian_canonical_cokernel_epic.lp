/* Epicity of the canonical coimage-to-image factor. */

require open emdash.emdash3_2_abelian_canonical_cokernel_factor;

symbol abelian_canonical_cokernel_candidate_epic_explicit
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
  : τ (@IsEpic C A
      (@computational_image_object C P t PA A B f)
      (@abelian_canonical_cokernel_candidate_explicit C P t PA A B f))
≔ @is_epic_comp C
    A
    (@computational_coimage_object C P t PA A B f)
    (@computational_image_object C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f)
    (@coimage_image_comparison C P t PA A B f)
    (@image_bimorphism_coimage_projection_epic C P t PA A B f)
    (@coimage_image_comparison_is_epic C P t PA M E A B f);
