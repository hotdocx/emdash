/*
  Reviewer-facing PSSS-03a example: an ordinary sieve is a Cat-valued higher
  sieve whose every value is a native subterminal category.

  The retained property evidence is proposition-valued and pullback preserves
  it. `Omega` is not declared here: setness of the classifier and strict
  contravariant family assembly remain explicit later gates.
*/

require open emdash.emdash3_2_sieves;

assert [C : Cat] ⊢
  IsSubterminalCat C
  ≡ `Σ_ obj_prop : τ (IsPropGrpd (Obj C)), @IsGroupoidalCat C;

assert [A : Grpd] (h : τ (IsPropGrpd A)) ⊢
  @path_cat_is_subterminal A h
  : τ (IsSubterminalCat (Path_cat A));

assert [C : Cat] (h : τ (IsSubterminalCat C)) ⊢
  @subterminal_cat_is_discrete C h
  : τ (IsDiscreteCat C);

assert [C : Cat] ⊢
  @is_subterminal_cat_evidence_is_prop C
  : τ (IsPropGrpd (IsSubterminalCat C));

assert [K : Cat] (U : τ (Obj K))
  (S : τ (@HigherSieve K U)) ⊢
  @is_ordinary_sieve_evidence_is_prop K U S
  : τ (IsPropGrpd (@IsOrdinarySieve K U S));

assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U)) ⊢
  @sieve_higher K V (@sieve_pullback K V U p R)
  ≡ @higher_sieve_pullback K V U p (@sieve_higher K U R);

assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U)) ⊢
  @sieve_subterminal K V (@sieve_pullback K V U p R)
  : τ (@IsOrdinarySieve K V
      (@higher_sieve_pullback K V U p (@sieve_higher K U R)));

// Retained evidence is propositionally unique, but package eta is not runtime.
assertnot [K : Cat] (U : τ (Obj K))
  (R : τ (@Sieve K U)) ⊢
  @sieve_pullback K U U (@id K U) R
  ≡ R;
