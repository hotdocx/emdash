/*
  Reviewer milestone: profunctor closed structure and weighted limits.

  These checks expose the fixed-endpoint computational core: tensor remains an
  opaque semantic owner, vertical eval/lambda are inverse by computation, a
  weighted cone is a profunctor implication, and the comparison interface
  supplies probe-stable inverse maps and right-adjoint preservation.
*/

require open emdash.emdash3_2;

assert [A B : Cat] ⊢
  Prof_base A B
  ≡ Product_cat (Op_cat A) B;

assert [A B : Cat] ⊢
  Prof A B
  ≡ Obj (Catd_cat (Product_cat (Op_cat A) B));

// The symbolic tensor has no selected general coend/coinserter semantics.
assertnot [A B X : Cat]
  (P : τ (Prof A B))
  (Q : τ (Prof B X)) ⊢
  @Prof_tensor A B X P Q
  ≡ @Const_catd (Product_cat (Op_cat A) X) Terminal_cat;

assert [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap P (@Prof_imply_cov A B X O Q))) ⊢
  @Prof_lambda_cov_map A B X P Q O
    (@Prof_eval_cov_map A B X P Q O t)
  ≡ t;

assert [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap (@Prof_tensor A B X P Q) O)) ⊢
  @Prof_eval_cov_map A B X P Q O
    (@Prof_lambda_cov_map A B X P Q O t)
  ≡ t;

assert [B J J' : Cat]
  (F : τ (Functor J B))
  (W : τ (Prof J' J)) ⊢
  @WeightedCone_prof B J J' F W
  ≡ @Prof_imply_cov
      B J' J
      (@Hom_prof J B F)
      W;

assert [B J J' I : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (M : τ (Functor I B))
  [R : τ (Prof I J')]
  (r : τ (ProfMap
      R
      (@Prof_imply_cov
        I J' J
        (@Hom_prof_along I J B M F)
        W))) ⊢
  @weighted_limit_cov_pull B J J' F W L isl I M R
    (@weighted_limit_cov_push B J J' F W L isl I M R r)
  ≡ r;

assert [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj)) ⊢
  @right_adjoint_preserves_weighted_limit_cov_comp
    B J J' A Ladj Radj W F L isl adj
  : τ (@IsWeightedLimit_cov_comp
      A J J'
      (@comp_cat_fapp0 J B A Radj F)
      W
      (@comp_cat_fapp0 J' B A Radj L));
