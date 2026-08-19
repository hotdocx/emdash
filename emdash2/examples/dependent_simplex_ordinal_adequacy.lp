/*
  Reviewer for the honest low-dimensional ordinal/dependent adequacy boundary.

  Dimension zero is a whole pointwise retraction. Dimension one observes the
  walking-arrow endpoints and generator. Generic join point betas compute the
  three shared triangle vertices; the native triangle is constructed once its
  one remaining dependent filler is supplied.
*/

require open emdash.emdash3_2_dependent_simplex_ordinal_adequacy;

// Zero-dimensional decoding is a pointwise retraction.
assert [C : Cat] (x : τ (Obj C)) ⊢
  @fapp0
    (Functor_cat Terminal_cat C)
    C
    (@ordinal_simplex0_observe_func C)
    (@fapp0
      C
      (Functor_cat Terminal_cat C)
      (@ordinal_simplex0_encode_func C)
      x)
  ≡ x;

// The converse terminal-source eta is deliberately not judgmental.
assertnot [C : Cat] (H : τ (Functor Terminal_cat C)) ⊢
  @fapp0
    C
    (Functor_cat Terminal_cat C)
    (@ordinal_simplex0_encode_func C)
    (@fapp0
      (Functor_cat Terminal_cat C)
      C
      (@ordinal_simplex0_observe_func C)
      H)
  ≡ H;

// Dimension-one observation is literally the source/target/generator edge.
assert [C : Cat] (H : τ (Functor WalkingArrow_cat C)) ⊢
  sigma_Fst (sigma_Snd (@ordinal_dependent_simplex1_observe C H))
  ≡ @ordinal_simplex1_target C H;

assert [C : Cat] (H : τ (Functor WalkingArrow_cat C)) ⊢
  sigma_Snd (sigma_Snd
    (@ordinal_dependent_simplex1_observe C H))
  ≡ @ordinal_simplex1_arrow C H;

// Generic join-eliminator point betas make all three shared vertices compute.
assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  @ordinal_simplex1_source C (@ordinal_simplex2_edge02 C H)
  ≡ @ordinal_simplex1_source C (@ordinal_simplex2_edge01 C H);

assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  @ordinal_simplex1_source C (@ordinal_simplex2_edge12 C H)
  ≡ @ordinal_simplex1_target C (@ordinal_simplex2_edge01 C H);

assert [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C)) ⊢
  @ordinal_simplex1_target C (@ordinal_simplex2_edge12 C H)
  ≡ @ordinal_simplex1_target C (@ordinal_simplex2_edge02 C H);

// Only one explicit dependent filler remains before the dimension-two
// observation can be assembled in the native code.
type λ C : Cat,
  λ H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C),
  λ alpha : τ (@OrdinalDependentSimplex2CanonicalFiller C H),
    @ordinal_dependent_simplex2_observe C H alpha;
