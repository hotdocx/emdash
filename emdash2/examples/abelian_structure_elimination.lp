/* Constructor computation of the derived Abelian-structure eliminator. */
require open emdash.emdash3_2_abelian_structure_elimination;

assert
  (C : Cat) (P : τ (Functor (Product_cat C C) C)) (t : τ (Obj C))
  (Q : τ (@ComputationalAbelianCategory C P t) → Grpd)
  (branch : Π PA : τ (@PreAbelianCategory C P t), Π M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)),
    Π E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)), τ (Q (@computational_abelian_category_intro C P t PA M E)))
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA))) (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  ⊢ @computational_abelian_ind C P t Q branch
      (@computational_abelian_category_intro C P t PA M E)
  ≡ branch PA M E;
