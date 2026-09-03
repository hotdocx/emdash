/* Canonical selected-kernel rows are computationally exact. */

require open emdash.emdash3_2_exactness_covers;
require open emdash.emdash3_2_abelian_image_bimorphisms;

symbol abelian_canonical_kernel_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalChainPair C
      (@abelian_stability_preadditive C P t Ab)
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f))
      A B)
≔ @computational_chain_pair_intro C
    (@abelian_stability_preadditive C P t Ab)
    (@computational_kernel_object C
      (@abelian_stability_preadditive C P t Ab) A B f
      ((@abelian_stability_kernels C P t Ab) A B f))
    A B
    (@computational_kernel_morphism C
      (@abelian_stability_preadditive C P t Ab) A B f
      ((@abelian_stability_kernels C P t Ab) A B f))
    f
    (@computational_kernel_annihilation C
      (@abelian_stability_preadditive C P t Ab) A B f
      ((@abelian_stability_kernels C P t Ab) A B f));

symbol abelian_canonical_kernel_homology
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalHomologyAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f))
      A B
      (@abelian_canonical_kernel_pair C P t Ab A B f))
≔ @computational_homology_at C P t
    (@abelian_stability_preabelian C P t Ab)
    (@computational_kernel_object C
      (@abelian_stability_preadditive C P t Ab) A B f
      ((@abelian_stability_kernels C P t Ab) A B f))
    A B
    (@abelian_canonical_kernel_pair C P t Ab A B f);

symbol abelian_canonical_kernel_boundary_id_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@= (Hom C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f))
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f)))
      (@computational_homology_boundary C P t
        (@abelian_stability_preabelian C P t Ab)
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab) A B f
          ((@abelian_stability_kernels C P t Ab) A B f))
        A B
        (@abelian_canonical_kernel_pair C P t Ab A B f)
        (@abelian_canonical_kernel_homology C P t Ab A B f))
      (@id C
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab) A B f
          ((@abelian_stability_kernels C P t Ab) A B f))))
≔ @computational_kernel_lift_unique_path C
    (@abelian_stability_preadditive C P t Ab)
    A B f
    ((@abelian_stability_kernels C P t Ab) A B f)
    (@computational_kernel_object C
      (@abelian_stability_preadditive C P t Ab) A B f
      ((@abelian_stability_kernels C P t Ab) A B f))
    (@computational_chain_pair_cone C
      (@abelian_stability_preadditive C P t Ab)
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f))
      A B
      (@abelian_canonical_kernel_pair C P t Ab A B f))
    (@id C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f)))
    (@eq_refl (Hom C
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab) A B f
          ((@abelian_stability_kernels C P t Ab) A B f))
        A)
      (@computational_kernel_morphism C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f)));

symbol abelian_canonical_kernel_exact
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalExactAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f))
      A B
      (@abelian_canonical_kernel_pair C P t Ab A B f)
      (@abelian_canonical_kernel_homology C P t Ab A B f))
≔ @is_epic_of_equal C
    (@computational_kernel_object C
      (@abelian_stability_preadditive C P t Ab) A B f
      ((@abelian_stability_kernels C P t Ab) A B f))
    (@computational_kernel_object C
      (@abelian_stability_preadditive C P t Ab) A B f
      ((@abelian_stability_kernels C P t Ab) A B f))
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab)
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f))
      A B
      (@abelian_canonical_kernel_pair C P t Ab A B f)
      (@abelian_canonical_kernel_homology C P t Ab A B f))
    (@id C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f)))
    (@abelian_canonical_kernel_boundary_id_path C P t Ab A B f)
    (@identity_is_epic C
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) A B f
        ((@abelian_stability_kernels C P t Ab) A B f)));
