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
