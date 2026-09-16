/* In-progress owner-local fragment; concatenate after the transformation-graph
   owner using README.md. Not a standalone module or a qualified library API. */
/* Reuse the internal transformation graph, retaining the chosen source lift A. */
require open emdash.emdash3_2_zero_arrow_cones;

symbol represented_comma_family_catd [X Y : Cat] (J : τ (Functor X Y))
  : τ (Catd (Op_cat X))
≔ @Pullback_catd (Op_cat X) (Op_cat Y)
    (@gray_transf_graph_target_base_catd Y) (@Op_func X Y J);

symbol represented_comma_family_reframe [X Y : Cat] (J : τ (Functor X Y))
  : τ (@Functord (Op_cat X) (@represented_comma_family_catd X Y J)
      (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)))
≔ @id_funcd (Op_cat X) (@represented_comma_family_catd X Y J);

symbol represented_comma_family_target [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X))
  : τ (Catd (Op_cat K))
≔ @Pullback_catd (Op_cat K) (Op_cat X)
    (@represented_comma_family_catd X Y J) (@Op_func K X A);

symbol represented_comma_family_section [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  : τ (Obj (@Pi_cat (Op_cat K) (@represented_comma_family_target K X Y J A)))
≔ @gray_transf_graph_target_sec K Y (@comp_cat_fapp0 K X Y J A) D h;

symbol represented_comma_family_underlying_func [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  : τ (Functor (Op_cat K) (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J)))
≔ @comp_cat_fapp0 (Op_cat K)
    (@Sigma_cat (Op_cat K) (@represented_comma_family_target K X Y J A))
    (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))
    (@sigma_pullback_total_func (Op_cat K) (Op_cat X) (@Op_func K X A)
      (@represented_comma_family_catd X Y J))
    (@section_total_func (Op_cat K) (@represented_comma_family_target K X Y J A)
      (@represented_comma_family_section K X Y J A D h));

symbol represented_comma_family_func [K X Y : Cat]
  (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  : τ (Functor K (@RepresentedComma_cat X Y J))
≔ @Op_func (Op_cat K)
    (@Sigma_cat (Op_cat X) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)))
    (@comp_cat_fapp0 (Op_cat K)
      (@Sigma_cat (Op_cat X) (@represented_comma_family_catd X Y J))
      (@Sigma_cat (Op_cat X) (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J)))
      (@sigma_map_func (Op_cat X) (@represented_comma_family_catd X Y J)
        (@homdc_op_edge_catd X Y (@represented_comma_prof X Y J))
        (@represented_comma_family_reframe X Y J))
      (@represented_comma_family_underlying_func K X Y J A D h));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (x : τ (Obj K)) ⊢
  @fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x
  ≡ @represented_comma_obj X Y J (@fapp0 K X A x) (@fapp0 K Y D x)
      (@tapp0_fapp0 K Y (@comp_cat_fapp0 K X Y J A) D x h);

// The source side is the actual action of the supplied whole family.
assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  (x y : τ (Obj K)) (g : τ (Hom K x y)) ⊢
  @fapp1_fapp0 (@RepresentedComma_cat X Y J) X (@represented_comma_source_func X Y J) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) y)
    (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x y g)
  ≡ @fapp1_fapp0 K X A x y g;

// The target side is the actual action of the supplied whole family.
assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  (x y : τ (Obj K)) (g : τ (Hom K x y)) ⊢
  @fapp1_fapp0 (@RepresentedComma_cat X Y J) Y (@represented_comma_target_func X Y J) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) y)
    (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x y g)
  ≡ @fapp1_fapp0 K Y D x y g;
