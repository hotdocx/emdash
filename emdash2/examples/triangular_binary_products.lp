/*
  Reviewer milestone: enhanced triangular chosen binary products.

  A selected whole P : C × C ⊢ C carries whole projection transfors and
  one whole represented-family pairing operation. Their stable projections
  implement Došen's K_1^a, K_2^a, pairing beta/distribution/eta, and the two
  selected §6.4 normalizations. Generic P action remains a distinct runtime
  normal form and agrees with the triangular map by an explicit path.
*/

require open emdash.emdash3_2_triangular_binary_products;

// The two projection transfors retain their full off-diagonal action.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (A0 A1 B0 B1 : τ (Obj C))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1)) ⊢
  @tapp1_fapp0
    (Product_cat C C) C
    P (@Product_projL_func C C)
    (@Product_pair C C A0 B0)
    (@Product_pair C C A1 B1)
    (@binary_products_proj1_transf C P BP)
    (@Product_pair
      (Hom_cat C A0 A1)
      (Hom_cat C B0 B1)
      f g)
  ≡ @binary_products_K1a_fapp0 C P BP B0 A0 A1 f;

// Pairing remains whole and iterable at the next base/hom action.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (X Y A0 A1 : τ (Obj C)) ⊢
  @tapp1_func
    (Op_cat C) Cat_cat
    (@binary_products_pair_source_family C A0 A1)
    (@binary_products_pair_target_family C P A0 A1)
    X Y
    (@binary_products_pair_transf C P BP A0 A1)
  : τ (Functor
      (Hom_cat (Op_cat C) X Y)
      (Functor_cat
        (@fapp0
          (Op_cat C) Cat_cat
          (@binary_products_pair_source_family C A0 A1)
          X)
        (@fapp0
          (Op_cat C) Cat_cat
          (@binary_products_pair_target_family C P A0 A1)
          Y)));

// First projection beta.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (X A B D : τ (Obj C))
  (f : τ (Hom C X A))
  (g : τ (Hom C X B))
  (h : τ (Hom C A D)) ⊢
  @comp_fapp0
    C X
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
    D
    (@binary_products_K1a_fapp0 C P BP B A D h)
    (@binary_products_pair_fapp0 C P BP X A B f g)
  ≡ @comp_fapp0 C X A D h f;

// The post-K_1(id) projection order joins the same beta directly.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (X A B : τ (Obj C))
  (f : τ (Hom C X A))
  (g : τ (Hom C X B)) ⊢
  @comp_fapp0
    C X
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
    A
    (@binary_products_proj1_fapp0 C P BP A B)
    (@binary_products_pair_fapp0 C P BP X A B f g)
  ≡ f;

// Pairing distribution.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (X0 X1 A B : τ (Obj C))
  (h : τ (Hom C X0 X1))
  (f : τ (Hom C X1 A))
  (g : τ (Hom C X1 B)) ⊢
  @comp_fapp0
    C X0 X1
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
    (@binary_products_pair_fapp0 C P BP X1 A B f g)
    h
  ≡ @binary_products_pair_fapp0
      C P BP X0 A B
      (@comp_fapp0 C X0 X1 A f h)
      (@comp_fapp0 C X0 X1 B g h);

// Product eta.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (A B : τ (Obj C)) ⊢
  @binary_products_pair_fapp0
    C P BP
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
    A B
    (@binary_products_proj1_fapp0 C P BP A B)
    (@binary_products_proj2_fapp0 C P BP A B)
  ≡ @id C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A B));

// One of the two symmetric §6.4 reductions.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (A B D0 D1 : τ (Obj C))
  (f : τ (Hom C B D0))
  (g : τ (Hom C B D1)) ⊢
  @binary_products_pair_fapp0
    C P BP
    (@fapp0 (Product_cat C C) C P (@Product_pair C C B A))
    D0 D1
    (@binary_products_K1a_fapp0 C P BP A B D0 f)
    (@binary_products_K1a_fapp0 C P BP A B D1 g)
  ≡ @binary_products_K1a_fapp0
      C P BP A B
      (@fapp0 (Product_cat C C) C P (@Product_pair C C D0 D1))
      (@binary_products_pair_fapp0 C P BP B D0 D1 f g);

// The semantic and triangular maps agree propositionally.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (A0 A1 B0 B1 : τ (Obj C))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1)) ⊢
  @binary_products_map_path C P BP A0 A1 B0 B1 f g
  : τ (@=
      (Hom C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A0 B0))
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A1 B1)))
      (@binary_products_semantic_map_fapp0
        C P BP A0 A1 B0 B1 f g)
      (@binary_products_map_fapp0
        C P BP A0 A1 B0 B1 f g));

// That agreement does not erase generic P action at runtime.
assertnot [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (A0 A1 B0 B1 : τ (Obj C))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C B0 B1)) ⊢
  @binary_products_semantic_map_fapp0
    C P BP A0 A1 B0 B1 f g
  ≡ @binary_products_map_fapp0
      C P BP A0 A1 B0 B1 f g;

// Ordinary hom-level uniqueness is derived from eta and distribution.
assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (X A B : τ (Obj C))
  (h : τ (Hom C X
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B)))) ⊢
  @binary_products_pair_unique_path C P BP X A B h
  : τ (@=
      (Hom C X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A B)))
      h
      (@binary_products_pair_reconstruct_fapp0 C P BP X A B h));
