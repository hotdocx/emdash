/*
  Emdash v3.2: the whole lax-arrow graph of a classified lax transformation.

  For L : LaxTransfor(F,G), let epsilon=lax_transfor(L). The graph is the functor

    B -> LaxArrow_cat(C)
    y |-> (F[y] -> G[y], epsilon[y]).

  Its arrow action is not a separately postulated naturality square. The
  construction applies fibrewise Sigma and pointwise opposite to the existing
  whole internal action, evaluates it on the canonical identity section,
  applies family-natural total base change, totalizes the resulting section,
  and finally takes the outer opposite. Generic fapp1 therefore retains every
  subsequent action.

  The represented-Sigma/opposite derivation is retained by the separate
  represented-comma-family owner. The public stable graph computes on objects and capped
  arrows to the standard directed square with literal sides F[g] and G[g].
  Its generic fapp1_func remains available for the next action.

  At g=id this selected graph beta has a documented overlap with retained
  generic normal-identity computation. The integration retires generic strict
  composition/naturality cuts while keeping normal identities and qualified
  constructor instances. Passing the selected observation checks does not
  establish general confluence. IsPseudoFunctor supplies fixed-forward
  OmegaEquivAlong evidence for the existing readable compositor; that property
  does not itself install the graph beta.
*/

require open emdash.emdash3_2_gray_interchanger_orientation;

// Public conventional cell from one classified lax transfor package.
symbol gray_transf_standard_cell
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Obj
      (@homdc_square_fibre
        C
        (@fapp0 B C F x)
        (@fapp0 B C F y)
        (@fapp0 B C G x)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G x
          (@lax_transfor B C F G L))
        (@tapp0_fapp0 B C F G y
          (@lax_transfor B C F G L))
        (@fapp1_fapp0 B C F x y g)
        (@fapp1_fapp0 B C G x y g)))
≔ @tapp1_post_laxity_cell
    B C F G
    (@lax_transfor B C F G L)
    x x y g (@id B x);

// Public conventional square from the same package.
symbol gray_transf_standard_square
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom
      (@LaxArrow_cat C)
      (@lax_edge C
        (@fapp0 B C F x)
        (@fapp0 B C G x)
        (@tapp0_fapp0 B C F G x
          (@lax_transfor B C F G L)))
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y
          (@lax_transfor B C F G L))))
≔ @lax_square
    C
    (@fapp0 B C F x)
    (@fapp0 B C F y)
    (@fapp0 B C G x)
    (@fapp0 B C G y)
    (@tapp0_fapp0 B C F G x (@lax_transfor B C F G L))
    (@tapp0_fapp0 B C F G y (@lax_transfor B C F G L))
    (@fapp1_fapp0 B C F x y g)
    (@fapp1_fapp0 B C G x y g)
    (@gray_transf_standard_cell B C F G L x y g);

/*
  Stable public transformation graph.

  The object and capped-arrow betas below are the selected computation of this
  classified lax graph. Generic hom action remains available beyond the capped
  observation. Its normal-identity overlap stays an explicit qualification;
  it is not a reason to restore generic strict composition/naturality cuts.
*/
injective symbol gray_transf_graph_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  : τ (Functor B (@LaxArrow_cat C));

rule @fapp0 _ _
      (@gray_transf_graph_func $B $C $F $G $L) $x
  ↪ @lax_edge
      $C
      (@fapp0 $B $C $F $x)
      (@fapp0 $B $C $G $x)
      (@tapp0_fapp0 $B $C $F $G $x
        (@lax_transfor $B $C $F $G $L));

rule @fapp1_fapp0
      _ _
      (@gray_transf_graph_func $B $C $F $G $L)
      $x $y $g
  ↪ @gray_transf_standard_square
      $B $C $F $G $L $x $y $g;

// Public object observation, retained as the graph functor's ordinary action.
symbol gray_transf_graph_obj
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  (y : τ (Obj B))
  : τ (Obj (@LaxArrow_cat C))
≔ @fapp0 B (@LaxArrow_cat C)
    (@gray_transf_graph_func B C F G L) y;

// Equality view of the runtime object beta
// (F[y],G[y],epsilon[y]); no additional Sigma eta is installed.
symbol gray_transf_graph_obj_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  (y : τ (Obj B))
  : τ (@=
      (Obj (@LaxArrow_cat C))
      (@gray_transf_graph_obj B C F G L y)
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y
          (@lax_transfor B C F G L))))
≔ @eq_refl
    (Obj (@LaxArrow_cat C))
    (@gray_transf_graph_obj B C F G L y);

// Whole arrow action; its next hom remains owned by generic fapp1_func.
symbol gray_transf_graph_arrow
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom
      (@LaxArrow_cat C)
      (@gray_transf_graph_obj B C F G L x)
      (@gray_transf_graph_obj B C F G L y))
≔ @fapp1_fapp0
    B (@LaxArrow_cat C)
    (@gray_transf_graph_func B C F G L)
    x y g;

// The source-side projection computes to F[g].
symbol gray_transf_graph_source_side
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
≔ @fapp1_fapp0
    (@LaxArrow_cat C) C (@cubical_src_func C)
    (@gray_transf_graph_obj B C F G L x)
    (@gray_transf_graph_obj B C F G L y)
    (@gray_transf_graph_arrow B C F G L x y g);

symbol gray_transf_graph_source_side_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (@=
      (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
      (@gray_transf_graph_source_side B C F G L x y g)
      (@fapp1_fapp0 B C F x y g))
≔ @eq_refl
    (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
    (@fapp1_fapp0 B C F x y g);

// The target-side projection computes to G[g].
symbol gray_transf_graph_target_side
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
≔ sigma_Fst
    (sigma_Snd
      (@gray_transf_graph_arrow B C F G L x y g));

symbol gray_transf_graph_target_side_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (@=
      (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
      (@gray_transf_graph_target_side B C F G L x y g)
      (@fapp1_fapp0 B C G x y g))
≔ @eq_refl
    (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
    (@fapp1_fapp0 B C G x y g);

// The remaining nested-Sigma projection computes to the standard cell.
symbol gray_transf_graph_cell
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Obj
      (@homdc_square_fibre
        C
        (@fapp0 B C F x)
        (@fapp0 B C F y)
        (@fapp0 B C G x)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G x
          (@lax_transfor B C F G L))
        (@tapp0_fapp0 B C F G y
          (@lax_transfor B C F G L))
        (@fapp1_fapp0 B C F x y g)
        (@gray_transf_graph_target_side
          B C F G L x y g)))
≔ sigma_Snd
    (sigma_Snd
      (@gray_transf_graph_arrow B C F G L x y g));

symbol gray_transf_graph_cell_projection_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (@=
      (Obj
        (@homdc_square_fibre
          C
          (@fapp0 B C F x)
          (@fapp0 B C F y)
          (@fapp0 B C G x)
          (@fapp0 B C G y)
          (@tapp0_fapp0 B C F G x
            (@lax_transfor B C F G L))
          (@tapp0_fapp0 B C F G y
            (@lax_transfor B C F G L))
          (@fapp1_fapp0 B C F x y g)
          (@fapp1_fapp0 B C G x y g)))
      (@gray_transf_graph_cell B C F G L x y g)
      (@gray_transf_standard_cell B C F G L x y g))
≔ @eq_refl
    (Obj
      (@homdc_square_fibre
        C
        (@fapp0 B C F x)
        (@fapp0 B C F y)
        (@fapp0 B C G x)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G x
          (@lax_transfor B C F G L))
        (@tapp0_fapp0 B C F G y
          (@lax_transfor B C F G L))
        (@fapp1_fapp0 B C F x y g)
        (@fapp1_fapp0 B C G x y g)))
    (@gray_transf_standard_cell B C F G L x y g);

// The graph is not capped at its square reading: another whole hom action is
// available for the recursive Gray-cube successor.
symbol gray_transf_graph_next_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (L : τ (@LaxTransfor B C F G))
  (x y : τ (Obj B))
  : τ (Functor
      (Hom_cat B x y)
      (Hom_cat
        (@LaxArrow_cat C)
        (@gray_transf_graph_obj B C F G L x)
        (@gray_transf_graph_obj B C F G L y)))
≔ @fapp1_func
    B (@LaxArrow_cat C)
    (@gray_transf_graph_func B C F G L)
    x y;
