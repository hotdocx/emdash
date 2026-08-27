/*
  Emdash v3.2: one profiled right-closed Gray slice.

  The tensor is an opaque stable category owner. Curry and uncurry are
  ordinary whole functors between the selected Gray-hom profile categories,
  each paired with supplied IsStrictFunctor evidence. Their whole
  equality-valued beta/eta comparisons
  assemble the existing OmegaEquivAlong Cat_cat interface. Coevaluation and
  evaluation are object projections at the selected strict identity packages.

  This is one right-closure boundary, not a full Crans--Gray tensor: it adds
  no mirror closure, tensor action in the parameters, monoidal coherence, or
  global migration of the prototype's strict functoriality/naturality cuts.
  The selected internal Hom uses the project's lax direction, confirmed by
  the typed I tensor I interchanger.
*/

require open emdash.emdash3_2_gray_profiles;

// Stable right-oriented tensor category owner; no monoidal structure claimed.
injective symbol GrayTensor_R
  (A B : Cat)
  : Cat;

// Source category of strict maps out of the selected tensor.
symbol GrayRightSource
  (A B C : Cat)
  : Cat
≔ @GrayHom_lax (@GrayTensor_R A B) C;

// Target category of strict outer maps into the lax-profiled inner Hom.
symbol GrayRightTarget
  (A B C : Cat)
  : Cat
≔ @GrayHom_lax A (@GrayHom_lax B C);

// Whole curry operation.
injective symbol gray_curry_R_func
  (A B C : Cat)
  : τ (@Functor
      (@GrayRightSource A B C)
      (@GrayRightTarget A B C));

// Supplied semantic strictness of the existing whole curry operation.
constant symbol gray_curry_R_is_strict
  (A B C : Cat)
  : τ (@IsStrictFunctor
      (@GrayRightSource A B C)
      (@GrayRightTarget A B C)
      (@gray_curry_R_func A B C));

symbol gray_curry_R_strict
  (A B C : Cat)
  : τ (@StrictFunctor
      (@GrayRightSource A B C)
      (@GrayRightTarget A B C)
    )
≔ @strict_functor_intro
    (@GrayRightSource A B C)
    (@GrayRightTarget A B C)
    (@gray_curry_R_func A B C)
    (@gray_curry_R_is_strict A B C);

// Whole uncurry operation.
injective symbol gray_uncurry_R_func
  (A B C : Cat)
  : τ (@Functor
      (@GrayRightTarget A B C)
      (@GrayRightSource A B C));

// Supplied semantic strictness of the existing whole uncurry operation.
constant symbol gray_uncurry_R_is_strict
  (A B C : Cat)
  : τ (@IsStrictFunctor
      (@GrayRightTarget A B C)
      (@GrayRightSource A B C)
      (@gray_uncurry_R_func A B C));

symbol gray_uncurry_R_strict
  (A B C : Cat)
  : τ (@StrictFunctor
      (@GrayRightTarget A B C)
      (@GrayRightSource A B C)
    )
≔ @strict_functor_intro
    (@GrayRightTarget A B C)
    (@GrayRightSource A B C)
    (@gray_uncurry_R_func A B C)
    (@gray_uncurry_R_is_strict A B C);

// Object projection of whole curry.
symbol gray_curry_R
  [A B C : Cat]
  (H : τ (Obj (@GrayRightSource A B C)))
  : τ (Obj (@GrayRightTarget A B C))
≔ @fapp0
    (@GrayRightSource A B C)
    (@GrayRightTarget A B C)
    (@gray_curry_R_func A B C)
    H;

// Object projection of whole uncurry.
symbol gray_uncurry_R
  [A B C : Cat]
  (K : τ (Obj (@GrayRightTarget A B C)))
  : τ (Obj (@GrayRightSource A B C))
≔ @fapp0
    (@GrayRightTarget A B C)
    (@GrayRightSource A B C)
    (@gray_uncurry_R_func A B C)
    K;

// Whole beta comparison: uncurry after curry is the source identity.
constant symbol gray_uncurry_curry_R_path
  (A B C : Cat)
  : τ (@=
      (Hom Cat_cat
        (@GrayRightSource A B C)
        (@GrayRightSource A B C))
      (@comp_cat_fapp0
        (@GrayRightSource A B C)
        (@GrayRightTarget A B C)
        (@GrayRightSource A B C)
        (@gray_uncurry_R_func A B C)
        (@gray_curry_R_func A B C))
      (@id_func (@GrayRightSource A B C)));

// Whole eta comparison: curry after uncurry is the target identity.
constant symbol gray_curry_uncurry_R_path
  (A B C : Cat)
  : τ (@=
      (Hom Cat_cat
        (@GrayRightTarget A B C)
        (@GrayRightTarget A B C))
      (@comp_cat_fapp0
        (@GrayRightTarget A B C)
        (@GrayRightSource A B C)
        (@GrayRightTarget A B C)
        (@gray_curry_R_func A B C)
        (@gray_uncurry_R_func A B C))
      (@id_func (@GrayRightTarget A B C)));

// Existing first-class omega-equivalence packages the selected right closure.
symbol gray_right_closure_omega
  (A B C : Cat)
  : τ (@OmegaEquivAlong
      Cat_cat
      (@GrayRightSource A B C)
      (@GrayRightTarget A B C)
      (@gray_curry_R_func A B C))
≔ @omega_equiv_along_intro
    Cat_cat
    (@GrayRightSource A B C)
    (@GrayRightTarget A B C)
    (@gray_curry_R_func A B C)
    (@gray_uncurry_R_func A B C)
    (@gray_uncurry_R_func A B C)
    (@gray_uncurry_curry_R_path A B C)
    (@gray_curry_uncurry_R_path A B C);

// Object-level beta is evaluation of the whole source cancellation path.
symbol gray_uncurry_curry_R_at
  [A B C : Cat]
  (H : τ (Obj (@GrayRightSource A B C)))
  : τ (@=
      (Obj (@GrayRightSource A B C))
      (@gray_uncurry_R A B C (@gray_curry_R A B C H))
      H)
≔ @eq_ap
    (Hom Cat_cat
      (@GrayRightSource A B C)
      (@GrayRightSource A B C))
    (Obj (@GrayRightSource A B C))
    (λ F : τ (@Functor
        (@GrayRightSource A B C)
        (@GrayRightSource A B C)),
      @fapp0
        (@GrayRightSource A B C)
        (@GrayRightSource A B C)
        F H)
    _ _
    (@gray_uncurry_curry_R_path A B C);

// Object-level eta is evaluation of the whole target cancellation path.
symbol gray_curry_uncurry_R_at
  [A B C : Cat]
  (K : τ (Obj (@GrayRightTarget A B C)))
  : τ (@=
      (Obj (@GrayRightTarget A B C))
      (@gray_curry_R A B C (@gray_uncurry_R A B C K))
      K)
≔ @eq_ap
    (Hom Cat_cat
      (@GrayRightTarget A B C)
      (@GrayRightTarget A B C))
    (Obj (@GrayRightTarget A B C))
    (λ F : τ (@Functor
        (@GrayRightTarget A B C)
        (@GrayRightTarget A B C)),
      @fapp0
        (@GrayRightTarget A B C)
        (@GrayRightTarget A B C)
        F K)
    _ _
    (@gray_curry_uncurry_R_path A B C);

// Coevaluation/introduction is curry applied to the tensor identity package.
symbol gray_coevaluation_R_strict
  (A B : Cat)
  : τ (@StrictFunctor
      A
      (@GrayHom_lax B (@GrayTensor_R A B)))
≔ @gray_curry_R
    A B (@GrayTensor_R A B)
    (@strict_identity (@GrayTensor_R A B));

symbol gray_coevaluation_R_func
  (A B : Cat)
  : τ (@Functor A (@GrayHom_lax B (@GrayTensor_R A B)))
≔ @strict_functor
    A
    (@GrayHom_lax B (@GrayTensor_R A B))
    (@gray_coevaluation_R_strict A B);

// Evaluation/elimination is uncurry applied to the internal-Hom identity package.
symbol gray_evaluation_R_strict
  (B C : Cat)
  : τ (@StrictFunctor
      (@GrayTensor_R (@GrayHom_lax B C) B)
      C)
≔ @gray_uncurry_R
    (@GrayHom_lax B C) B C
    (@strict_identity (@GrayHom_lax B C));

symbol gray_evaluation_R_func
  (B C : Cat)
  : τ (@Functor
      (@GrayTensor_R (@GrayHom_lax B C) B)
      C)
≔ @strict_functor
    (@GrayTensor_R (@GrayHom_lax B C) B)
    C
    (@gray_evaluation_R_strict B C);
