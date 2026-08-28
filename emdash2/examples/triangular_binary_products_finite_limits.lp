/*
  Reviewer milestone: a supplied strict weighted-product capability turns the
  triangular product object into the existing BinaryProductPresentation and
  relates both selected projections propositionally. No automatic DefIso is
  claimed.
*/

require open emdash.emdash3_2_triangular_binary_products_finite_limits;

assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [BP : τ (@BinaryProducts C P)]
  (K : τ (@BinaryProductsWeightedComp C P BP))
  (A B : τ (Obj C)) ⊢
  @binary_products_weighted_presentation C P BP K A B
  : τ (@BinaryProductPresentation C A B);

assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [BP : τ (@BinaryProducts C P)]
  (K : τ (@BinaryProductsWeightedComp C P BP))
  (A B : τ (Obj C)) ⊢
  @binary_product_object C A B
    (@binary_products_weighted_presentation C P BP K A B)
  ≡ @fapp0 (Product_cat C C) C P (@Product_pair C C A B);

assert [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [BP : τ (@BinaryProducts C P)]
  (K : τ (@BinaryProductsWeightedComp C P BP))
  (A B : τ (Obj C)) ⊢
  @binary_products_weighted_proj1_path C P BP K A B
  : τ (@= (Hom C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A B)) A)
      (@selected_binary_product_projection0
        C A B
        (@binary_products_weighted_presentation C P BP K A B))
      (@binary_products_proj1_fapp0 C P BP A B));
