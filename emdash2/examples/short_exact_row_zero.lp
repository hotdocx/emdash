/* Both original endpoints are zero without replacing their objects. */
require open emdash.emdash3_2_short_exact_row_zero;
constant symbol C : Cat;
constant symbol P : τ (Functor (Product_cat C C) C);
constant symbol t : τ (Obj C);
constant symbol PA : τ (@PreAbelianCategory C P t);
constant symbol A : τ (Obj C);
constant symbol B : τ (Obj C);
constant symbol D : τ (Obj C);
constant symbol row : τ (@ComputationalShortExactRow C P t PA A B D);
constant symbol zero_B : τ (@= (Hom C B B) (@id C B)
  (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) B B));
assert ⊢ @short_exact_row_source_identity_zero C P t PA A B D row zero_B
  : τ (@= (Hom C A A) (@id C A)
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) A A));
assert ⊢ @short_exact_row_target_identity_zero C P t PA A B D row zero_B
  : τ (@= (Hom C D D) (@id C D)
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) D D));
/* The middle object's property is not itself a proof at another object. */
assertnot ⊢ zero_B : τ (@= (Hom C A A) (@id C A)
  (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) A A));
