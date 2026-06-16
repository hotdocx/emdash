/*
  Reviewer milestone: directed Sigma totals.

  Sigma totals are dependent sums of directed Cat-valued families. These checks
  expose the total-category constructor, first projection, constant-family
  product specialization, and Sigma-map object action.
*/

require open emdash.emdash3_2;

assert [K : Cat] (E : τ (Catd K)) ⊢
  @fapp0 (Catd_cat K) Cat_cat (Sigma_func K) E ≡ Sigma_cat E;

assert [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  fapp0 (Sigma_proj1_func E) (Struct_sigma k u) ≡ k;

assert [K A : Cat] ⊢
  @Sigma_cat K (@Const_catd K A) ≡ Product_cat K A;

assert [K : Cat] (E D : τ (Catd K)) (η : τ (Functord E D))
  (k : τ (Obj K)) (u : τ (Obj (Fibre_cat E k))) ⊢
  @fapp0 (@Sigma_cat K E) (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma k u)
    ≡ @Struct_sigma
        (Obj K)
        (λ kk : τ (Obj K), Obj (Fibre_cat D kk))
        k
        (@fapp0 (Fibre_cat E k) (Fibre_cat D k)
          (@tapp0_fapp0 K Cat_cat E D k η)
          u);
