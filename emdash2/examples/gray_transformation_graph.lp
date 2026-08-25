/*
  Reviewer example: an ordinary transformation has one whole lax-arrow graph.

    epsilon : F => G
      |-> gray_transf_graph_func(epsilon) : B -> LaxArrow(C).

  Objects read as the edges epsilon[y].  On g:x->y, the first side computes
  to F[g]; the opposite nested-Sigma projections expose the retained target
  side and the existing internal-action filler.  The filler therefore has the
  native directed boundary

    target_side(g) o epsilon[x]
      ==> epsilon[y] o F[g].

  The generic lax target side is intentionally not equated with the separately
  named G[g].  Another whole hom action remains available for Gray-cube
  recursion.  No graph primitive, pointwise naturality record, Sigma eta,
  endpoint collapse, or graph-specific rule is introduced.
*/

require open emdash.emdash3_2_gray_transformation_graph;

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G)) ⊢
  @gray_transf_graph_func B C F G epsilon
  : τ (Functor B (@LaxArrow_cat C));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  (y : τ (Obj B)) ⊢
  @gray_transf_graph_obj_path B C F G epsilon y
  : τ (@=
      (Obj (@LaxArrow_cat C))
      (@gray_transf_graph_obj B C F G epsilon y)
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y epsilon)));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_source_side_path B C F G epsilon x y g
  : τ (@=
      (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
      (@gray_transf_graph_source_side B C F G epsilon x y g)
      (@fapp1_fapp0 B C F x y g));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_target_side B C F G epsilon x y g
  : τ (Hom C (@fapp0 B C G x) (@fapp0 B C G y));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_cell B C F G epsilon x y g
  : τ (Obj
      (@homdc_square_fibre
        C
        (@fapp0 B C F x)
        (@fapp0 B C F y)
        (@fapp0 B C G x)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G x epsilon)
        (@tapp0_fapp0 B C F G y epsilon)
        (@fapp1_fapp0 B C F x y g)
        (@gray_transf_graph_target_side
          B C F G epsilon x y g)));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj B)) ⊢
  @gray_transf_graph_next_func B C F G epsilon x y
  : τ (Functor
      (Hom_cat B x y)
      (Hom_cat
        (@LaxArrow_cat C)
        (@gray_transf_graph_obj B C F G epsilon x)
        (@gray_transf_graph_obj B C F G epsilon y)));
