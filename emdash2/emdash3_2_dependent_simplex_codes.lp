/*
  Intrinsically indexed codes for the flagged dependent-simplex tower.

  A raw code is indexed by its ambient category C, dimension n, and decoded
  category K. The zero constructor decodes to C. A successor stores one flag
  object x : Obj(K) and is indexed by PathOut_K(x). Thus the code contains no
  syntax for arbitrary categories and the decoder never reimplements
  Hom/Sigma/homd semantics: its category index is the native result.

  `DependentSimplexCode(C,n)` existentially packages K when callers do not
  need the index explicitly. `DependentSimplexEndpointView` separately carries
  formal and readable endpoints plus their typed equality, as required by the
  dimension-four residual. Existing `FaceCode(succ p,succ n)` remains the
  boundary-reference language. This curated inductive is standard-library
  infrastructure, not a user-defined inductive facility; it adds no runtime
  rewrite beyond the raw-wrapper decoding rule and no proof-time unifier.
*/

require open emdash.emdash3_2_dependent_simplex_dimension4;

// Raw flag code indexed by its already-decoded category.
inductive RawDependentSimplexCodeData : Cat → nat → Cat → TYPE ≔
| raw_dependent_simplex_zero (C : Cat)
    : RawDependentSimplexCodeData C zero C
| raw_dependent_simplex_step
    (C : Cat) (n : nat) (K : Cat)
    (c : RawDependentSimplexCodeData C n K)
    (x : τ (Obj K))
    : RawDependentSimplexCodeData C (succ n) (@PathOut_cat K x);

// Groupoid wrapper for the intrinsically indexed raw data.
injective symbol RawDependentSimplexCode
  (C : Cat)
  (n : τ Nat_grpd)
  (K : Cat)
  : Grpd;

rule τ (@RawDependentSimplexCode $C $n $K)
  ↪ RawDependentSimplexCodeData $C $n $K;

// Existential public package when the decoded category index is hidden.
symbol DependentSimplexCode
  (C : Cat)
  (n : τ Nat_grpd)
  : Grpd
≔ @Σ_ (Obj Cat_cat)
    (λ K : τ (Obj Cat_cat), @RawDependentSimplexCode C n K);

// Decoding is the intrinsic category index, not an interpretation of syntax.
symbol dependent_simplex_code_decode_cat
  [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  : Cat
≔ sigma_Fst c;

// Raw proof that the package has the decoded category index.
symbol dependent_simplex_code_raw
  [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  : τ (@RawDependentSimplexCode
      C n (@dependent_simplex_code_decode_cat C n c))
≔ sigma_Snd c;

// Zero-dimensional code.
symbol dependent_simplex_code_zero
  (C : Cat)
  : τ (@DependentSimplexCode C zero)
≔ @Struct_sigma
    (Obj Cat_cat)
    (λ K : τ (Obj Cat_cat), @RawDependentSimplexCode C zero K)
    C
    (@raw_dependent_simplex_zero C);

// Successor code: retain the previous code and one native flag object.
symbol dependent_simplex_code_step
  [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (x : τ (Obj (@dependent_simplex_code_decode_cat C n c)))
  : τ (@DependentSimplexCode C (succ n))
≔ @Struct_sigma
    (Obj Cat_cat)
    (λ K : τ (Obj Cat_cat), @RawDependentSimplexCode C (succ n) K)
    (@PathOut_cat (@dependent_simplex_code_decode_cat C n c) x)
    (@raw_dependent_simplex_step
      C n
      (@dependent_simplex_code_decode_cat C n c)
      (@dependent_simplex_code_raw C n c)
      x);

// Existing nonempty face codes are the boundary-reference language.
symbol DependentSimplexFaceRef
  (p n : τ Nat_grpd)
  : Grpd
≔ @FaceCode (succ p) (succ n);

// Formal/readable endpoint view attached to a decoded recursive frame.
symbol DependentSimplexEndpointView
  [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  : Grpd
≔ `Σ_ formal : τ (Obj (@dependent_simplex_code_decode_cat C n c)),
   `Σ_ readable : τ (Obj (@dependent_simplex_code_decode_cat C n c)),
     @= (Obj (@dependent_simplex_code_decode_cat C n c)) formal readable;

symbol dependent_simplex_endpoint_view
  [C : Cat]
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (formal readable : τ (Obj (@dependent_simplex_code_decode_cat C n c)))
  (comparison : τ (@=
    (Obj (@dependent_simplex_code_decode_cat C n c))
    formal readable))
  : τ (@DependentSimplexEndpointView C n c)
≔ Struct_sigma formal (Struct_sigma readable comparison);

// Selected native codes through the dimension-four acceptance case.
symbol dependent_simplex_code1
  (C : Cat)
  (x0 : τ (Obj C))
  : τ (@DependentSimplexCode C (succ zero))
≔ @dependent_simplex_code_step
    C zero (@dependent_simplex_code_zero C) x0;

symbol dependent_simplex_code2
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  : τ (@DependentSimplexCode C (succ (succ zero)))
≔ @dependent_simplex_code_step
    C (succ zero)
    (@dependent_simplex_code1 C x0)
    e01;

symbol dependent_simplex_code3
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  : τ (@DependentSimplexCode C (succ (succ (succ zero))))
≔ @dependent_simplex_code_step
    C (succ (succ zero))
    (@dependent_simplex_code2 C x0 e01)
    t012;

symbol dependent_simplex_code4
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)))
  : τ (@DependentSimplexCode C
      (succ (succ (succ (succ zero)))))
≔ @dependent_simplex_code_step
    C (succ (succ (succ zero)))
    (@dependent_simplex_code3 C x0 e01 t012)
    s0123;
