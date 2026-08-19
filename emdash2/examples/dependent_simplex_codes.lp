/* Reviewer for the intrinsically indexed dependent-simplex codes. */

require open emdash.emdash3_2_dependent_simplex_codes;

// Raw constructors recover their intrinsic decoded-category indices.
type λ C : Cat, @raw_dependent_simplex_zero C;

type λ C : Cat, λ n : τ Nat_grpd, λ K : Cat,
  λ c : τ (@RawDependentSimplexCode C n K),
  λ x : τ (Obj K),
    @raw_dependent_simplex_step C n K c x;

// Zero and successor decoding are structural.
assert (C : Cat) ⊢
  @dependent_simplex_code_decode_cat C zero
    (@dependent_simplex_code_zero C)
  ≡ C;

assert [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (x : τ (Obj (@dependent_simplex_code_decode_cat C n c))) ⊢
  @dependent_simplex_code_decode_cat C (succ n)
    (@dependent_simplex_code_step C n c x)
  ≡ @PathOut_cat (@dependent_simplex_code_decode_cat C n c) x;

// The selected codes reproduce the checked native classifiers through four.
assert [C : Cat]
  (x0 : τ (Obj C)) ⊢
  @dependent_simplex_code_decode_cat C (succ zero)
    (@dependent_simplex_code1 C x0)
  ≡ @DependentSimplex1_cat C x0;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0))) ⊢
  @dependent_simplex_code_decode_cat C (succ (succ zero))
    (@dependent_simplex_code2 C x0 e01)
  ≡ @DependentSimplex2_cat C x0 e01;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01))) ⊢
  @dependent_simplex_code_decode_cat C (succ (succ (succ zero)))
    (@dependent_simplex_code3 C x0 e01 t012)
  ≡ @DependentSimplex3_cat C x0 e01 t012;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012))) ⊢
  @dependent_simplex_code_decode_cat C (succ (succ (succ (succ zero))))
    (@dependent_simplex_code4 C x0 e01 t012 s0123)
  ≡ @DependentSimplex4_cat C x0 e01 t012 s0123;

// A successor code does not collapse back to its predecessor category.
assertnot [C : Cat] (x0 : τ (Obj C)) ⊢
  @dependent_simplex_code_decode_cat C (succ zero)
    (@dependent_simplex_code1 C x0)
  ≡ C;

// Existing face codes are reused rather than duplicated.
assert (p n : τ Nat_grpd) ⊢
  @DependentSimplexFaceRef p n
  ≡ @FaceCode (succ p) (succ n);

// Formal/readable endpoint views retain both endpoints and their comparison.
assert [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (formal readable : τ (Obj (@dependent_simplex_code_decode_cat C n c)))
  (comparison : τ (@=
    (Obj (@dependent_simplex_code_decode_cat C n c))
    formal readable)) ⊢
  sigma_Fst (@dependent_simplex_endpoint_view
    C n c formal readable comparison)
  ≡ formal;

assert [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (formal readable : τ (Obj (@dependent_simplex_code_decode_cat C n c)))
  (comparison : τ (@=
    (Obj (@dependent_simplex_code_decode_cat C n c))
    formal readable)) ⊢
  sigma_Fst (sigma_Snd (@dependent_simplex_endpoint_view
    C n c formal readable comparison))
  ≡ readable;

assert [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (formal readable : τ (Obj (@dependent_simplex_code_decode_cat C n c)))
  (comparison : τ (@=
    (Obj (@dependent_simplex_code_decode_cat C n c))
    formal readable)) ⊢
  sigma_Snd (sigma_Snd (@dependent_simplex_endpoint_view
    C n c formal readable comparison))
  ≡ comparison;
