/* Ordinary Δ⊣P presentation over the original BinaryProducts capability.
   The two structural operations extend today's opaque classifiers: they
   are explicit model obligations, not derivations from their current β
   interface. Whole counit and unit components use the original projections
   and diagonal pairing; native adjunction mates own inverse computation. */
require open emdash.emdash3_2_triangular_binary_products;
require open emdash.emdash3_2_one_cat_adjunction_families;
require open emdash.emdash3_2_product_family_views;

// Explicit ordinary structural closure, not a derived whole core inverse.
constant symbol one_cat_product_category [C D : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (D1 : τ (IsNCat (cat_succ cat_zero) D))
  : τ (IsNCat (cat_succ cat_zero) (Product_cat C D));

// Explicit structural presentation of the existing chosen products as Δ⊣P.
injective symbol one_cat_binary_product_adjunction [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  : τ (@Adjunction C (Product_cat C C) (@product_diagonal_func C) P);

// Counit = (π₁,π₂), as one whole product-valued transformation.
rule @counit_adj_transf _ _ _ _ (@one_cat_binary_product_adjunction $C _ $P $BP)
  ↪ Struct_sigma (@binary_products_proj1_transf $C $P $BP) (@binary_products_proj2_transf $C $P $BP);

// The unit component is the original selected diagonal pairing.
rule @tapp0_fapp0 _ _ _ _ $X
    (@unit_adj_transf _ _ _ _ (@one_cat_binary_product_adjunction $C _ $P $BP))
  ↪ @binary_products_pair_fapp0 $C $P $BP $X $X $X (@id $C $X) (@id $C $X);
