/*
  Reviewer example: an ordinary transformation has one whole lax-arrow graph.

    epsilon : F => G
      |-> gray_transf_graph_func(epsilon) : B -> LaxArrow(C).

  Objects compute to the edges epsilon[y]. On g:x->y, the capped arrow
  computes to the literal standard directed square

    G[g] o epsilon[x]
      ==> epsilon[y] o F[g].

  Its filler is extracted from the existing post/left internal action at
  id_x; no independent naturality field is postulated. The whole hom action
  remains available through generic fapp1_func. At an identity arrow the graph
  beta deliberately overlaps the historical globally strict functor cut; the
  intended lax computation is retained pending the documented cut migration.
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
  @gray_transf_graph_target_side_path B C F G epsilon x y g
  : τ (@=
      (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
      (@gray_transf_graph_target_side B C F G epsilon x y g)
      (@fapp1_fapp0 B C G x y g));

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
        (@fapp1_fapp0 B C G x y g)));

assert [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_cell_projection_path B C F G epsilon x y g
  : τ (@=
      (Obj
        (@homdc_square_fibre
          C
          (@fapp0 B C F x)
          (@fapp0 B C F y)
          (@fapp0 B C G x)
          (@fapp0 B C G y)
          (@tapp0_fapp0 B C F G x epsilon)
          (@tapp0_fapp0 B C F G y epsilon)
          (@fapp1_fapp0 B C F x y g)
          (@fapp1_fapp0 B C G x y g)))
      (@gray_transf_graph_cell B C F G epsilon x y g)
      (@gray_transf_standard_cell B C F G epsilon x y g));

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
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @gray_transf_graph_arrow B C F G epsilon x y g
  ≡ @gray_transf_standard_square B C F G epsilon x y g;

// Prototype-policy negative: the selected graph beta wins at the public head.
// The historical generic strict-identity cut remains a diagnosed competing
// reduction until its planned profile-local migration.
assertnot [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  (x : τ (Obj B)) ⊢
  @gray_transf_graph_arrow B C F G epsilon x x (@id B x)
  ≡ @id
      (@LaxArrow_cat C)
      (@gray_transf_graph_obj B C F G epsilon x);

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
