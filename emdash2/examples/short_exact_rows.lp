/* Generic row coupling and selected image-row computations. */

require open emdash.emdash3_2_selected_short_exact_rows;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t PA A B D pair))
  ⊢ @computational_short_exact_row_pair C P t PA A B D
      (@computational_short_exact_row_intro C P t PA A B D pair short)
  ≡ pair;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t PA A B D pair))
  ⊢ @computational_short_exact_row_evidence C P t PA A B D
      (@computational_short_exact_row_intro C P t PA A B D pair short)
  ≡ short;

assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair other : τ (@ComputationalChainPair C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t PA A B D pair))
  ⊢ @computational_short_exact_row_intro C P t PA A B D other short
  : τ (@ComputationalShortExactRow C P t PA A B D);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA))
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_short_exact_row_pair C P t PA
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@selected_short_exact_row C P t PA A B f))
  ≡ (@computational_kernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_cokernel_morphism C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_image C P t PA A B f));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA))
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@computational_short_exact_row_pair C P t PA
    (@computational_kernel_object C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@selected_short_exact_row C P t PA A B f))
  ≡ (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B : τ (Obj C))
  (f : τ (Hom C A B))
  ⊢ @computational_short_exact_row_evidence C P t PA (@computational_kernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) B
    (@computational_cokernel_object C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_cokernel_morphism C (@additive_preadditive C P t
    (@preabelian_additive C P t PA)) A B f (@preabelian_cokernel C P t PA A B f))
    (@computational_image C P t PA A B f)) B (@computational_cokernel_object C
    (@additive_preadditive C P t (@preabelian_additive C P t PA)) A B f
    (@preabelian_cokernel C P t PA A B f)) (@selected_short_exact_row C P t PA A B f)
  ≡ @selected_short_exact_evidence C P t PA A B f;
