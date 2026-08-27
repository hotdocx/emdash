/*
  Reviewer example: one profiled right-closed Gray slice.

  Curry and uncurry are whole functors between selected strict-object/lax-arrow
  Hom profiles, each paired with semantic IsStrictFunctor evidence. Their
  beta/eta boundary is equality-valued and iterable; it is not a new
  judgmental object fold.
*/

require open emdash.emdash3_2_gray_right_closure;

assert [A B C : Cat] ⊢
  @GrayRightSource A B C
  ≡ @GrayHom_lax (@GrayTensor_R A B) C;

assert [A B C : Cat] ⊢
  @GrayRightTarget A B C
  ≡ @GrayHom_lax A (@GrayHom_lax B C);

assert [A B C : Cat] ⊢
  @strict_functor_underlying
      (@GrayRightSource A B C)
      (@GrayRightTarget A B C)
      (@gray_curry_R_strict A B C)
  ≡ @gray_curry_R_func A B C;

assert [A B C : Cat] ⊢
  @strict_functor_evidence
    (@GrayRightSource A B C)
    (@GrayRightTarget A B C)
    (@gray_curry_R_strict A B C)
  ≡ @gray_curry_R_is_strict A B C;

assert [A B C : Cat] ⊢
  @strict_functor_underlying
      (@GrayRightTarget A B C)
      (@GrayRightSource A B C)
      (@gray_uncurry_R_strict A B C)
  ≡ @gray_uncurry_R_func A B C;

assert [A B C : Cat] ⊢
  @strict_functor_evidence
    (@GrayRightTarget A B C)
    (@GrayRightSource A B C)
    (@gray_uncurry_R_strict A B C)
  ≡ @gray_uncurry_R_is_strict A B C;

// The transpose retains the whole Hom action between transformation towers.
assert [A B C : Cat]
  (H K : τ (Obj (@GrayRightSource A B C))) ⊢
  @fapp1_func
    (@GrayRightSource A B C)
    (@GrayRightTarget A B C)
    (@gray_curry_R_func A B C)
    H K
  : τ (@Functor
      (Hom_cat (@GrayRightSource A B C) H K)
      (Hom_cat
        (@GrayRightTarget A B C)
        (@gray_curry_R A B C H)
        (@gray_curry_R A B C K)));

// The existing omega-equivalence owner packages the same uncurry both ways.
assert [A B C : Cat] ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (@GrayRightSource A B C)
    (@GrayRightTarget A B C)
    (@gray_curry_R_func A B C)
    (@gray_right_closure_omega A B C)
  ≡ @gray_uncurry_R_func A B C;

assert [A B C : Cat] ⊢
  @omega_equiv_along_right_inv
    Cat_cat
    (@GrayRightSource A B C)
    (@GrayRightTarget A B C)
    (@gray_curry_R_func A B C)
    (@gray_right_closure_omega A B C)
  ≡ @gray_uncurry_R_func A B C;

// Whole beta and eta evaluate to comparisons on strict-functor packages.
assert [A B C : Cat]
  (H : τ (Obj (@GrayRightSource A B C))) ⊢
  @gray_uncurry_curry_R_at A B C H
  : τ (@=
      (Obj (@GrayRightSource A B C))
      (@gray_uncurry_R A B C (@gray_curry_R A B C H))
      H);

assert [A B C : Cat]
  (K : τ (Obj (@GrayRightTarget A B C))) ⊢
  @gray_curry_uncurry_R_at A B C K
  : τ (@=
      (Obj (@GrayRightTarget A B C))
      (@gray_curry_R A B C (@gray_uncurry_R A B C K))
      K);

// Coevaluation and evaluation are derived at selected identity packages.
assert [A B : Cat] ⊢
  @gray_coevaluation_R_strict A B
  ≡ @gray_curry_R
      A B (@GrayTensor_R A B)
      (@strict_identity (@GrayTensor_R A B));

assert [A B : Cat] ⊢
  @gray_coevaluation_R_func A B
  ≡ @strict_functor
      A
      (@GrayHom_lax B (@GrayTensor_R A B))
      (@gray_coevaluation_R_strict A B);

assert [B C : Cat] ⊢
  @gray_evaluation_R_strict B C
  ≡ @gray_uncurry_R
      (@GrayHom_lax B C) B C
      (@strict_identity (@GrayHom_lax B C));

assert [B C : Cat] ⊢
  @gray_evaluation_R_func B C
  ≡ @strict_functor
      (@GrayTensor_R (@GrayHom_lax B C) B)
      C
      (@gray_evaluation_R_strict B C);

// The one-sided tensor/profile boundary is not the Cartesian scaffold.
assertnot [A B : Cat] ⊢
  @GrayTensor_R A B
  ≡ @Product_cat A B;

assertnot [A B C : Cat] ⊢
  @GrayRightTarget A B C
  ≡ @Functor_cat A (@Functor_cat B C);

// Beta remains whole equality evidence rather than a runtime object fold.
assertnot [A B C : Cat]
  (H : τ (Obj (@GrayRightSource A B C))) ⊢
  @gray_uncurry_R A B C (@gray_curry_R A B C H)
  ≡ H;
