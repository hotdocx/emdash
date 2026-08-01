/*
  Reviewer-facing PSSS-02 example: contravariant Yoneda, conventional slices,
  and the Cat-valued higher-sieve classifier reuse existing hom, Sigma, Catd,
  and pullback owners.

  A `HigherSieve` is deliberately not an ordinary subterminal sieve.  The
  ordinary classifier and the name `Omega` remain behind the later
  truncation/subterminal design gate.
*/

require open emdash.emdash3_2_presheaves;

// The facade-level Yoneda object evaluates to the represented hom category.
assert [K : Cat] (U V : τ (Obj K)) ⊢
  Fibre_cat (@yoneda_psh K U) V
  ≡ Hom_cat K V U;

// Its arrow action is inherited from the internal-hom owner.
assert [K : Cat]
  (V U W : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @tapp0_fapp0
    (Op_cat K)
    Cat_cat
    (@yoneda_psh K V)
    (@yoneda_psh K U)
    W
    (@fapp1_fapp0
      K
      (@Psh_cat K)
      (@yoneda_psh_func K)
      V U p)
  ≡ @hom_postcomp_func
      K K (@id_func K)
      W V U p;

// The visible conventional slice is opposite to the restriction total.
assert [K : Cat] (U : τ (Obj K)) ⊢
  @Slice_cat K U
  ≡ Op_cat (@Sigma_cat (Op_cat K) (@yoneda_psh K U));

// Both presentations compare to one stable Catd category.
assert [K : Cat] (U : τ (Obj K)) ⊢
  @eq_refl Cat_grpd (@HigherSieve_cat K U)
  : τ (@= Cat_grpd
      (@HigherSieve_cat K U)
      (@Catd_cat (@Into_restr_cat K U)));

assert [K : Cat] (U : τ (Obj K)) ⊢
  @eq_refl Cat_grpd (@Psh_cat (@Slice_cat K U))
  : τ (@= Cat_grpd
      (@Psh_cat (@Slice_cat K U))
      (@Catd_cat (@Into_restr_cat K U)));

// Lambdapi does not chain those two experimental unification steps.
assertnot [K : Cat] (U : τ (Obj K)) ⊢
  @HigherSieve_cat K U
  ≡ @Psh_cat (@Slice_cat K U);

// The maximal higher sieve is stable under restriction.
assert [K : Cat]
  (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @fapp0
    (@HigherSieve_cat K U)
    (@HigherSieve_cat K V)
    (@fapp1_fapp0
      (Op_cat K)
      Cat_cat
      (@HigherSieveClassifier K)
      U V p)
    (@maximal_higher_sieve K U)
  ≡ @maximal_higher_sieve K V;
