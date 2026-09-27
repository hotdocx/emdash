/*
  Reviewer example: one classified lax transfor has one whole lax-arrow graph.

    L : LaxTransfor(F,G)
      |-> gray_transf_graph_func(L) : B -> LaxArrow(C).

  Objects compute to the carrier components. On g:x->y, the capped arrow
  computes to the conventional square

    G[g] o epsilon[x]
      ==> epsilon[y] o F[g],

  using the one existing internal-action cell and the evidence packaged in L.
*/

require open emdash.emdash3_2_gray_transformation_graph;

symbol graph_example_epsilon
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  : τ (Transf F G)
≔ @lax_transfor B C F G L;

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G)) ⊢
  @gray_transf_graph_func B C F G L
  : τ (Functor B (@LaxArrow_cat C));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  (y : τ (Obj B)) ⊢
  @gray_transf_graph_obj_path B C F G L y
  : τ (@=
      (Obj (@LaxArrow_cat C))
      (@gray_transf_graph_obj B C F G L y)
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y (@graph_example_epsilon B C F G L))));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_source_side_path B C F G L x y g
  : τ (@=
      (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
      (@gray_transf_graph_source_side B C F G L x y g)
      (@fapp1_fapp0 B C F x y g));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_target_side_path B C F G L x y g
  : τ (@=
      (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
      (@gray_transf_graph_target_side B C F G L x y g)
      (@fapp1_fapp0 B C G x y g));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_cell_projection_path B C F G L x y g
  : τ (@=
      (Obj
        (@homdc_square_fibre
          C
          (@fapp0 B C F x)
          (@fapp0 B C F y)
          (@fapp0 B C G x)
          (@fapp0 B C G y)
          (@tapp0_fapp0 B C F G x (@graph_example_epsilon B C F G L))
          (@tapp0_fapp0 B C F G y (@graph_example_epsilon B C F G L))
          (@fapp1_fapp0 B C F x y g)
          (@fapp1_fapp0 B C G x y g)))
      (@gray_transf_graph_cell B C F G L x y g)
      (@gray_transf_standard_cell B C F G L x y g));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_standard_square B C F G L x y g
  : τ (Hom
      (@LaxArrow_cat C)
      (@lax_edge C
        (@fapp0 B C F x)
        (@fapp0 B C G x)
        (@tapp0_fapp0 B C F G x (@graph_example_epsilon B C F G L)))
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y (@graph_example_epsilon B C F G L))));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_arrow B C F G L x y g
  ≡ @gray_transf_standard_square B C F G L x y g;

// Normal-lax identity remains the selected later migration boundary.
assertnot [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  (x : τ (Obj B)) ⊢
  @gray_transf_graph_arrow B C F G L x x (@id B x)
  ≡ @id
      (@LaxArrow_cat C)
      (@gray_transf_graph_obj B C F G L x);

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  (x y : τ (Obj B)) ⊢
  @gray_transf_graph_next_func B C F G L x y
  : τ (Functor
      (Hom_cat B x y)
      (Hom_cat
        (@LaxArrow_cat C)
        (@gray_transf_graph_obj B C F G L x)
        (@gray_transf_graph_obj B C F G L y)));
