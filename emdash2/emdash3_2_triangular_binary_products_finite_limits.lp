/*
  Assumption-explicit bridge from triangular binary products to the existing
  computational weighted-limit presentation.

  `BinaryProducts(C,P)` alone does not construct the kernel's strict
  `DefIso`-based `IsWeightedLimit_cov_comp`. This module therefore accepts a
  supplied computational weighted witness for every pair, together with paths
  identifying its two selected projections with the triangular projections.
  It then constructs `BinaryProductPresentation(C,A,B)` transparently.

  The module adds no runtime rule, proof-time unifier, automatic `DefIso`
  witness, or reverse assembly from unrelated per-pair choices to a whole P.
*/

require open emdash.emdash3_2_triangular_binary_products;
require open emdash.emdash3_2_finite_limits;

// Supplied strict weighted comparison and projection compatibility at every pair.
symbol BinaryProductsWeightedComp
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  : Grpd
≔ @Pi_grpd
    (Obj C)
    (λ A : τ (Obj C),
      @Pi_grpd
        (Obj C)
        (λ B : τ (Obj C),
          `Σ_ W : τ (@IsBinaryProduct_comp
              C A B
              (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))),
            @Product_grpd
              (@= (Hom C
                    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
                    A)
                  (@binary_product_projection0
                    C A B
                    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
                    W)
                  (@binary_products_proj1_fapp0 C P BP A B))
              (@= (Hom C
                    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
                    B)
                  (@binary_product_projection1
                    C A B
                    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
                    W)
                  (@binary_products_proj2_fapp0 C P BP A B))));

// Supplied strict weighted comparison at A,B.
symbol binary_products_weighted_comp
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [BP : τ (@BinaryProducts C P)]
  (K : τ (@BinaryProductsWeightedComp C P BP))
  (A B : τ (Obj C))
  : τ (@IsBinaryProduct_comp
      C A B
      (@fapp0 (Product_cat C C) C P (@Product_pair C C A B)))
≔ sigma_Fst (K A B);

// Transparent selected weighted presentation at A,B.
symbol binary_products_weighted_presentation
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [BP : τ (@BinaryProducts C P)]
  (K : τ (@BinaryProductsWeightedComp C P BP))
  (A B : τ (Obj C))
  : τ (@BinaryProductPresentation C A B)
≔ @binary_product_intro
    C A B
    (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
    (@binary_products_weighted_comp C P BP K A B);

// First weighted projection agrees propositionally with the triangular one.
symbol binary_products_weighted_proj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [BP : τ (@BinaryProducts C P)]
  (K : τ (@BinaryProductsWeightedComp C P BP))
  (A B : τ (Obj C))
  : τ (@= (Hom C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A B)) A)
      (@binary_product_projection0
        C A B
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
        (@binary_products_weighted_comp C P BP K A B))
      (@binary_products_proj1_fapp0 C P BP A B))
≔ sigma_Fst (sigma_Snd (K A B));

// Second weighted projection agrees propositionally with the triangular one.
symbol binary_products_weighted_proj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [BP : τ (@BinaryProducts C P)]
  (K : τ (@BinaryProductsWeightedComp C P BP))
  (A B : τ (Obj C))
  : τ (@= (Hom C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A B)) B)
      (@binary_product_projection1
        C A B
        (@fapp0 (Product_cat C C) C P (@Product_pair C C A B))
        (@binary_products_weighted_comp C P BP K A B))
      (@binary_products_proj2_fapp0 C P BP A B))
≔ sigma_Snd (sigma_Snd (K A B));
