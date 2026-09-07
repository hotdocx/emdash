/*
  Dependent elimination of the existing computational Abelian structure.

  This is a definition through the two existing Sigma eliminators. Its
  constructor case exposes PA and normality directly, avoiding a forced
  comparison of an opaque structure with its eta reconstruction.
*/
require open emdash.emdash3_2_abelian_categories;

symbol computational_abelian_ind
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Q : τ (@ComputationalAbelianCategory C P t) → Grpd)
  (branch : Π PA : τ (@PreAbelianCategory C P t),
    Π M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)),
    Π E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)), τ (Q (@computational_abelian_category_intro C P t PA M E)))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  : τ (Q Ab)
≔ @sigma_ind (@PreAbelianCategory C P t) (λ PA : τ (@PreAbelianCategory C P t), (@Product_grpd (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)) (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))) Q
    (λ PA : τ (@PreAbelianCategory C P t),
      λ normal : τ (@Product_grpd (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)) (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA))),
        @sigma_ind (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)) (λ _ : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)), (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
          (λ normal0 : τ (@Product_grpd (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)) (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA))),
            Q (@Struct_sigma (@PreAbelianCategory C P t) (λ PA : τ (@PreAbelianCategory C P t), (@Product_grpd (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)) (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))) PA normal0))
          (λ M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)), λ E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)), branch PA M E)
          normal)
    Ab;
