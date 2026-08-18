/*
  Reviewer example: one profiled right-closed Gray slice.

  Curry and uncurry are whole computationally strict functors between
  selected strict-object/lax-arrow Hom profiles.  Their beta/eta boundary is
  equality-valued and iterable; it is not a new judgmental object fold.
*/

require open emdash.emdash3_2_gray_right_closure;

assert [A B C : Cat] ⊢
  @GrayRightSource A B C
  ≡ @GrayHom_lax (@GrayTensor_R A B) C;

assert [A B C : Cat] ⊢
  @GrayRightTarget A B C
  ≡ @GrayHom_lax A (@GrayHom_lax B C);

assert [A B C : Cat] ⊢
  @gray_curry_R_func A B C
  ≡ @strict_functor_carrier
      (@GrayRightSource A B C)
      (@GrayRightTarget A B C)
      (@gray_curry_R_data A B C);

assert [A B C : Cat] ⊢
  @gray_uncurry_R_func A B C
  ≡ @strict_functor_carrier
      (@GrayRightTarget A B C)
      (@GrayRightSource A B C)
      (@gray_uncurry_R_data A B C);

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

// Whole beta and eta evaluate to comparisons on strict-functor codes.
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

// Coevaluation and evaluation are derived at selected identity codes.
assert [A B : Cat] ⊢
  @gray_coevaluation_R_data A B
  ≡ @gray_curry_R
      A B (@GrayTensor_R A B)
      (@strict_identity_data (@GrayTensor_R A B));

assert [A B : Cat] ⊢
  @gray_coevaluation_R_func A B
  ≡ @strict_functor_carrier
      A
      (@GrayHom_lax B (@GrayTensor_R A B))
      (@gray_coevaluation_R_data A B);

assert [B C : Cat] ⊢
  @gray_evaluation_R_data B C
  ≡ @gray_uncurry_R
      (@GrayHom_lax B C) B C
      (@strict_identity_data (@GrayHom_lax B C));

assert [B C : Cat] ⊢
  @gray_evaluation_R_func B C
  ≡ @strict_functor_carrier
      (@GrayTensor_R (@GrayHom_lax B C) B)
      C
      (@gray_evaluation_R_data B C);

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
