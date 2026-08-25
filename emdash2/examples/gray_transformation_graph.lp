/*
  Reviewer example: an ordinary transformation has one whole lax-arrow graph.

    epsilon : F => G
      |-> gray_transf_graph_func(epsilon) : B -> LaxArrow(C).

  Objects read as the edges epsilon[y].  On g:x->y, the strictified/internal
  whole graph exposes F[g], retains its second-side construction history, and
  retains another whole hom action for Gray-cube recursion.

  Separately, `gray_transf_standard_square(epsilon,g)` is the literal standard
  directed square

    G[g] o epsilon[x]
      ==> epsilon[y] o F[g].

  Its filler is extracted from the existing post/left internal action at
  id_x; no independent naturality field is postulated.  Assembling these
  literal squares into a whole graph is deliberately deferred until a
  normal-lax/lax-map profile can express their identity and composition
  coherence without conflicting with the present strict Functor cuts.
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
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_standard_cell B C F G epsilon x y g
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
        (@fapp1_fapp0 B C G x y g)));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_standard_square B C F G epsilon x y g
  : τ (Hom
      (@LaxArrow_cat C)
      (@lax_edge C
        (@fapp0 B C F x)
        (@fapp0 B C G x)
        (@tapp0_fapp0 B C F G x epsilon))
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y epsilon)));

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
