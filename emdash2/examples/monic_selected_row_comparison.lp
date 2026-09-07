/* Generic comparison-point beta retains its selected isomorphism and reconstruction. */

require open emdash.emdash3_2_monic_selected_row_comparison;

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
  ⊢ sigma_Fst (@monic_selected_row_comparison C P t PA A B f normal monic)
  ≡ @monic_image_iso C P t PA A B f normal monic;

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
  ⊢ sigma_Snd (@monic_selected_row_comparison C P t PA A B f normal monic)
  ≡ @monic_image_comparison_path C P t PA A B f;
