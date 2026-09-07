/* Kernel rows use their supplied whole kernel; homology retains the PA selection. */

require open emdash.emdash3_2_short_exact_rows;
require open emdash.emdash3_2_exactness_covers;

symbol kernel_short_exact_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [B D : τ (Obj C)]
  (p : τ (Hom C B D))
  (W : τ (@ComputationalKernel C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p))
  : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA))
    (@computational_kernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p W) B D)
≔ @computational_chain_pair_intro C (@additive_preadditive C P t (@preabelian_additive C P t PA))
  (@computational_kernel_object C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) B D p W) B D
    (@computational_kernel_morphism C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B D p W) p (@computational_kernel_annihilation C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W);

// Kernel universality supplies an exact cover with the identity as covering map.
symbol kernel_row_exact_cover
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [B D : τ (Obj C)]
  (p : τ (Hom C B D))
  (W : τ (@ComputationalKernel C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p))
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p T))
  : τ (@ComputationalExactCoverWitness C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
    (@kernel_short_exact_pair C P t PA B D p W) T cone)
≔ @computational_exact_cover_intro C P t PA (@computational_kernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
  (@kernel_short_exact_pair C P t PA B D p W) T cone
    T (@id C T) (@identity_is_epic C T)
    (@computational_kernel_lift C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B D p W T cone)
    (@computational_kernel_lift_path C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B D p W T cone);

symbol kernel_row_exact_covers
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [B D : τ (Obj C)]
  (p : τ (Hom C B D))
  (W : τ (@ComputationalKernel C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p))
  : τ (@HasComputationalExactCovers C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
    (@kernel_short_exact_pair C P t PA B D p W))
≔ λ T : τ (Obj C), λ cone : τ (@WeakKernelAnnihilator C (@additive_preadditive C P t
  (@preabelian_additive C P t PA)) B D p T),
    @kernel_row_exact_cover C P t PA B D p W T cone;

symbol kernel_row_exact
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [B D : τ (Obj C)]
  (p : τ (Hom C B D))
  (W : τ (@ComputationalKernel C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p))
  : τ (@computational_exact_at_selected C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
    (@kernel_short_exact_pair C P t PA B D p W))
≔ @computational_exact_at_from_covers C P t PA (@computational_kernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
  (@kernel_short_exact_pair C P t PA B D p W)
    (@computational_homology_at C P t PA (@computational_kernel_object C
      (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
      (@kernel_short_exact_pair C P t PA B D p W)) (@kernel_row_exact_covers C P t PA B D p W);

symbol kernel_short_exact_evidence
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [B D : τ (Obj C)]
  (p : τ (Hom C B D))
  (W : τ (@ComputationalKernel C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p))
  (epic : τ (@IsEpic C B D p))
  : τ (@ComputationalShortExactTriple C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
    (@kernel_short_exact_pair C P t PA B D p W))
≔ @computational_short_exact_intro C P t PA (@computational_kernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
  (@kernel_short_exact_pair C P t PA B D p W)
    (@computational_kernel_morphism_is_monic C (@additive_preadditive C P t
      (@preabelian_additive C P t PA)) B D p W)
    epic (@kernel_row_exact C P t PA B D p W);

symbol kernel_short_exact_row
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [B D : τ (Obj C)]
  (p : τ (Hom C B D))
  (W : τ (@ComputationalKernel C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B D p))
  (epic : τ (@IsEpic C B D p))
  : τ (@ComputationalShortExactRow C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D)
≔ @computational_short_exact_row_intro C P t PA (@computational_kernel_object C
  (@additive_preadditive C P t (@preabelian_additive C P t PA)) B D p W) B D
  (@kernel_short_exact_pair C P t PA B D p W)
    (@kernel_short_exact_evidence C P t PA B D p W epic);
