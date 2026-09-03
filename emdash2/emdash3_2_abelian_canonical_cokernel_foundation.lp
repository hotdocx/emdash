/* Canonical cokernel row with one explicit pre-Abelian owner. */

require open emdash.emdash3_2_exactness_covers;
require open emdash.emdash3_2_abelian_image_bimorphisms;

symbol abelian_canonical_cokernel_pair_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalChainPair C
      (@preabelian_preadditive C P t PA)
      A B
      (@computational_cokernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_cokernel C P t PA A B f)))
≔ @computational_chain_pair_intro C
    (@preabelian_preadditive C P t PA)
    A B
    (@computational_cokernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    f
    (@computational_cokernel_morphism C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_annihilation C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f));

symbol abelian_canonical_cokernel_homology_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@ComputationalHomologyAt C P t PA
      A B
      (@computational_cokernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_cokernel C P t PA A B f))
      (@abelian_canonical_cokernel_pair_explicit C P t PA A B f))
≔ @computational_homology_at C P t PA
    A B
    (@computational_cokernel_object C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f))
    (@abelian_canonical_cokernel_pair_explicit C P t PA A B f);

symbol abelian_canonical_cokernel_image_cone_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (@WeakKernelAnnihilator C
      (@preabelian_preadditive C P t PA)
      B
      (@computational_cokernel_object C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_cokernel C P t PA A B f))
      (@computational_cokernel_morphism C
        (@preabelian_preadditive C P t PA) A B f
        (@preabelian_cokernel C P t PA A B f))
      A)
≔ @Struct_sigma
    (Hom C A B)
    (λ h : τ (Hom C A B),
      @= (Hom C A
        (@computational_cokernel_object C
          (@preabelian_preadditive C P t PA) A B f
          (@preabelian_cokernel C P t PA A B f)))
        (@comp_fapp0 C _ _ _
          (@computational_cokernel_morphism C
            (@preabelian_preadditive C P t PA) A B f
            (@preabelian_cokernel C P t PA A B f)) h)
        (@preadditive_hom_zero C
          (@preabelian_preadditive C P t PA) A
          (@computational_cokernel_object C
            (@preabelian_preadditive C P t PA) A B f
            (@preabelian_cokernel C P t PA A B f))))
    f
    (@computational_cokernel_annihilation C
      (@preabelian_preadditive C P t PA) A B f
      (@preabelian_cokernel C P t PA A B f));

symbol abelian_canonical_cokernel_candidate_explicit
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B : τ (Obj C)]
  (f : τ (Hom C A B))
  : τ (Hom C A (@computational_image_object C P t PA A B f))
≔ @comp_fapp0 C _ _ _
    (@coimage_image_comparison C P t PA A B f)
    (@computational_coimage_projection C P t PA A B f);
