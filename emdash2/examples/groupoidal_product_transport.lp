/*
  Focused reviewer for the first rule-free groupoidal-closure comparison.
  It checks the canonical Path-product functor, its explicit homwise inverse,
  both inverse laws, and the whole identity-on-objects/hom-carrier-equivalence
  certificate without collapsing the two category presentations globally.
*/

require open emdash.emdash3_2_groupoidal_closure;

assert [A B : Grpd] ⊢ path_product_compare_func
  : τ (@Functor
      (Path_cat (Product_grpd A B))
      (Product_cat (Path_cat A) (Path_cat B)));

// The comparison is literally identity on objects.
assert [A B : Grpd] (p : τ (Product_grpd A B)) ⊢
  @fapp0
    (Path_cat (Product_grpd A B))
    (@PathProduct_cat A B)
    (@path_product_compare_func A B)
    p
  ≡ p;

// Its actual arrow action is propositionally the explicit component split.
assert [A B : Grpd]
       [p q : τ (Product_grpd A B)]
       (w : τ (@PathProductHom_grpd A B p q)) ⊢
  path_product_compare_hom_agrees w
  : τ (@=
      (@PathProductComponentHom_grpd A B p q)
      (@path_product_compare_hom A B p q w)
      (@path_product_split A B p q w));

// The explicit split and join maps cancel in both directions.
assert [A B : Grpd]
       [p q : τ (Product_grpd A B)]
       (w : τ (@PathProductHom_grpd A B p q)) ⊢
  path_product_join_split w
  : τ (@=
      (@PathProductHom_grpd A B p q)
      (@path_product_join A B p q
        (@path_product_split A B p q w))
      w);

assert [A B : Grpd]
       [p q : τ (Product_grpd A B)]
       (h : τ (@PathProductComponentHom_grpd A B p q)) ⊢
  path_product_split_join h
  : τ (@=
      (@PathProductComponentHom_grpd A B p q)
      (@path_product_split A B p q
        (@path_product_join A B p q h))
      h);

// The package uses the actual comparison action as its selected forward map.
assert [A B : Grpd]
       [p q : τ (Product_grpd A B)]
       (w : τ (@PathProductHom_grpd A B p q)) ⊢
  type_equiv_to
    (@path_product_compare_hom_type_equiv A B p q)
    w
  ≡ @path_product_compare_hom A B p q w;

// The explicit join is retained as the selected inverse map.
assert [A B : Grpd]
       [p q : τ (Product_grpd A B)]
       (h : τ (@PathProductComponentHom_grpd A B p q)) ⊢
  type_equiv_from
    (@path_product_compare_hom_type_equiv A B p q)
    h
  ≡ @path_product_join A B p q h;

assert [A B : Grpd] ⊢ path_product_comparison_evidence
  : τ (@PathProductComparisonEvidence A B);

assert [A B : Grpd]
       (p q : τ (Product_grpd A B)) ⊢
  path_product_comparison_hom_equiv p q
  : τ (@TypeEquiv
      (@PathProductHom_grpd A B p q)
      (@PathProductComponentHom_grpd A B p q));

// The named bridge preserves the distinct higher normal forms.
assertnot [A B : Grpd] ⊢
  Path_cat (Product_grpd A B)
  ≡ Product_cat (Path_cat A) (Path_cat B);

/*
  Product transport needs no extra computation rule.  Coordinate paths may
  be paired, transported simultaneously, or factored in either coordinate
  order; ordinary path induction supplies the comparison and coherence data.
*/

assert [A B : Grpd]
       (a : τ A) (b : τ B) ⊢
  product_pair_path_refl a b
  : τ (@=
      (@PathProductHom_grpd
        A B
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b))
      (@product_pair_path A B a a b b
        (@eq_refl A a)
        (@eq_refl B b))
      (@eq_refl
        (Product_grpd A B)
        (@Product_pair_grpd A B a b)));

assert [A B : Grpd]
       (P : τ (Product_grpd A B) → Grpd)
       (a : τ A) (b : τ B)
       (u : τ (P (@Product_pair_grpd A B a b))) ⊢
  product_path_transport_pair_refl P a b u
  : τ (@=
      (P (@Product_pair_grpd A B a b))
      (@product_path_transport
        A B P
        (@Product_pair_grpd A B a b)
        (@Product_pair_grpd A B a b)
        (@product_pair_path A B a a b b
          (@eq_refl A a)
          (@eq_refl B b))
        u)
      u);

assert [A B : Grpd]
       (P : τ (Product_grpd A B) → Grpd)
       [a0 a1 : τ A] [b0 b1 : τ B]
       (p : τ (a0 = a1)) (q : τ (b0 = b1))
       (u : τ (P (@Product_pair_grpd A B a0 b0))) ⊢
  product_transport_direct_agrees_base_then_fibre P p q u
  : τ (@=
      (P (@Product_pair_grpd A B a1 b1))
      (@product_transport_direct A B P a0 a1 b0 b1 p q u)
      (@product_transport_base_then_fibre
        A B P a0 a1 b0 b1 p q u));

assert [A B : Grpd]
       (P : τ (Product_grpd A B) → Grpd)
       [a0 a1 : τ A] [b0 b1 : τ B]
       (p : τ (a0 = a1)) (q : τ (b0 = b1))
       (u : τ (P (@Product_pair_grpd A B a0 b0))) ⊢
  product_transport_direct_agrees_fibre_then_base P p q u
  : τ (@=
      (P (@Product_pair_grpd A B a1 b1))
      (@product_transport_direct A B P a0 a1 b0 b1 p q u)
      (@product_transport_fibre_then_base
        A B P a0 a1 b0 b1 p q u));

assert [A B : Grpd]
       (P : τ (Product_grpd A B) → Grpd)
       [a0 a1 : τ A] [b0 b1 : τ B]
       (p : τ (a0 = a1)) (q : τ (b0 = b1))
       (u : τ (P (@Product_pair_grpd A B a0 b0))) ⊢
  product_transport_coherence_diamond P p q u
  : τ (@=
      (P (@Product_pair_grpd A B a1 b1))
      (@product_transport_base_then_fibre
        A B P a0 a1 b0 b1 p q u)
      (@product_transport_fibre_then_base
        A B P a0 a1 b0 b1 p q u));

// The structured family is the same product-indexed Grpd family on objects.
assert [A B : Grpd]
       (P : τ (Product_grpd A B) → Grpd)
       (s : τ (Product_grpd A B)) ⊢
  Fibre_cat (@ProductPathFamily_catd A B P) s
  ≡ Path_cat (P s);

// Both structured interfaces agree with the one primitive right-J transport.
assert [A B : Grpd]
       (P : τ (Product_grpd A B) → Grpd)
       [s t : τ (Product_grpd A B)]
       (u : τ (P s)) (r : τ (s = t)) ⊢
  product_path_structured_transport_agrees_primitive P u r
  : τ (@=
      (P t)
      (@product_path_structured_transport A B P s t u r)
      (@product_path_transport A B P s t r u));

assert [A B : Grpd]
       (P : τ (Product_grpd A B) → Grpd)
       [s t : τ (Product_grpd A B)]
       (u : τ (P s)) (r : τ (s = t)) ⊢
  product_path_structured_induction_agrees_primitive P u r
  : τ (@=
      (P t)
      (@product_path_structured_induction A B P s t u r)
      (@product_path_transport A B P s t r u));
