/* Reviewer-facing derived image/coimage and comparison consumers. */

require open emdash.emdash3_2_abelian_images;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B : τ (Obj C))
  (m : τ (Hom C A B))
  (W : τ (@ComputationalKernel C S A B m))
  (monic : τ (@IsMonic C A B m))
  ⊢ @monic_kernel_morphism_zero_path C S A B m W monic
  : τ (@= (Hom C (@computational_kernel_object C S A B m W) A)
      (@computational_kernel_morphism C S A B m W)
      (@preadditive_hom_zero C S
        (@computational_kernel_object C S A B m W) A));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B : τ (Obj C))
  (e : τ (Hom C A B))
  (W : τ (@ComputationalCokernel C S A B e))
  (epic : τ (@IsEpic C A B e))
  ⊢ @epic_cokernel_morphism_zero_path C S A B e W epic
  : τ (@= (Hom C B (@computational_cokernel_object C S A B e W))
      (@computational_cokernel_morphism C S A B e W)
      (@preadditive_hom_zero C S B
        (@computational_cokernel_object C S A B e W)));

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (P : τ (@PreAbelianCategory C Prod t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @computational_coimage C Prod t P A B f
  : τ (@ComputationalCokernel C
      (@preabelian_preadditive C Prod t P)
      (@computational_kernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f))
      A
      (@computational_kernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_kernel C Prod t P A B f)));

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (P : τ (@PreAbelianCategory C Prod t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @computational_image C Prod t P A B f
  : τ (@ComputationalKernel C
      (@preabelian_preadditive C Prod t P)
      B
      (@computational_cokernel_object C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C Prod t P) A B f
        (@preabelian_cokernel C Prod t P A B f)));

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (P : τ (@PreAbelianCategory C Prod t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @coimage_image_comparison C Prod t P A B f
  : τ (Hom C
      (@computational_coimage_object C Prod t P A B f)
      (@computational_image_object C Prod t P A B f));

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (P : τ (@PreAbelianCategory C Prod t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @coimage_image_comparison_path C Prod t P A B f
  : τ (@= (Hom C (@computational_coimage_object C Prod t P A B f) B)
      (@comp_fapp0 C
        (@computational_coimage_object C Prod t P A B f)
        (@computational_image_object C Prod t P A B f) B
        (@computational_image_embedding C Prod t P A B f)
        (@coimage_image_comparison C Prod t P A B f))
      (@coimage_to_target C Prod t P A B f));

assert
  (C : Cat)
  (Prod : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (P : τ (@PreAbelianCategory C Prod t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @coimage_image_factorization_path C Prod t P A B f
  : τ (@= (Hom C A B)
      (@comp_fapp0 C A
        (@computational_image_object C Prod t P A B f) B
        (@computational_image_embedding C Prod t P A B f)
        (@comp_fapp0 C A
          (@computational_coimage_object C Prod t P A B f)
          (@computational_image_object C Prod t P A B f)
          (@coimage_image_comparison C Prod t P A B f)
          (@computational_coimage_projection C Prod t P A B f)))
      f);
