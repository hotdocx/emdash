/*
  Emdash v3.2: the whole lax-arrow graph of an ordinary transformation.

  For epsilon : F => G with F,G : B -> C, the graph is the functor

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

  At g=id this selected graph beta overlaps the historical global strict
  functor-identity cut.  That diagnostic overlap is deliberately accepted by
  the repository's prototype policy: the global strict cuts are scheduled for
  later profile-local migration and must not veto intended lax computation.
  IsPseudoFunctor already supplies fixed-forward
  OmegaEquivAlong evidence for the existing readable compositor of a selected
  carrier; it does not install this graph beta or disable the global cuts.
*/

require open emdash.emdash3_2_gray_interchanger_orientation;

// Standard lax-naturality filler with literal sides F[g] and G[g], extracted
// from the existing post/left whole action at the identity source arrow.
symbol gray_transf_standard_cell
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
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
        (@fapp1_fapp0 B C G x y g)))
≔ @tapp1_post_laxity_cell
    B C F G epsilon
    x x y g (@id B x);

// Constructor-visible standard square.
symbol gray_transf_standard_square
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom
      (@LaxArrow_cat C)
      (@lax_edge C
        (@fapp0 B C F x)
        (@fapp0 B C G x)
        (@tapp0_fapp0 B C F G x epsilon))
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y epsilon)))
≔ @lax_square
    C
    (@fapp0 B C F x)
    (@fapp0 B C F y)
    (@fapp0 B C G x)
    (@fapp0 B C G y)
    (@tapp0_fapp0 B C F G x epsilon)
    (@tapp0_fapp0 B C F G y epsilon)
    (@fapp1_fapp0 B C F x y g)
    (@fapp1_fapp0 B C G x y g)
    (@gray_transf_standard_cell B C F G epsilon x y g);

/*
  Stable public transformation graph.

  The object and capped-arrow betas below are the selected intended
  computation.  The identity instance is knowingly nonjoinable with the
  historical generic strict-functor cut.  Keep this rule and migrate the
  generic cut later; do not suppress the lax graph computation merely to make
  the temporary prototype globally strict.
*/
injective symbol gray_transf_graph_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  : τ (Functor B (@LaxArrow_cat C));

rule @fapp0 _ _
      (@gray_transf_graph_func $B $C $F $G $epsilon) $x
  ↪ @lax_edge
      $C
      (@fapp0 $B $C $F $x)
      (@fapp0 $B $C $G $x)
      (@tapp0_fapp0 $B $C $F $G $x $epsilon);

rule @fapp1_fapp0
      _ _
      (@gray_transf_graph_func $B $C $F $G $epsilon)
      $x $y $g
  ↪ @gray_transf_standard_square
      $B $C $F $G $epsilon $x $y $g;

// Public object observation, retained as the graph functor's ordinary action.
symbol gray_transf_graph_obj
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  (y : τ (Obj B))
  : τ (Obj (@LaxArrow_cat C))
≔ @fapp0 B (@LaxArrow_cat C)
    (@gray_transf_graph_func B C F G epsilon) y;

// Equality view of the runtime object beta
// (F[y],G[y],epsilon[y]); no additional Sigma eta is installed.
symbol gray_transf_graph_obj_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  (y : τ (Obj B))
  : τ (@=
      (Obj (@LaxArrow_cat C))
      (@gray_transf_graph_obj B C F G epsilon y)
      (@lax_edge C
        (@fapp0 B C F y)
        (@fapp0 B C G y)
        (@tapp0_fapp0 B C F G y epsilon)))
≔ @eq_refl
    (Obj (@LaxArrow_cat C))
    (@gray_transf_graph_obj B C F G epsilon y);

// Whole arrow action; its next hom remains owned by generic fapp1_func.
symbol gray_transf_graph_arrow
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom
      (@LaxArrow_cat C)
      (@gray_transf_graph_obj B C F G epsilon x)
      (@gray_transf_graph_obj B C F G epsilon y))
≔ @fapp1_fapp0
    B (@LaxArrow_cat C)
    (@gray_transf_graph_func B C F G epsilon)
    x y g;

// The source-side projection computes to F[g].
symbol gray_transf_graph_source_side
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
≔ @fapp1_fapp0
    (@LaxArrow_cat C) C (@cubical_src_func C)
    (@gray_transf_graph_obj B C F G epsilon x)
    (@gray_transf_graph_obj B C F G epsilon y)
    (@gray_transf_graph_arrow B C F G epsilon x y g);

symbol gray_transf_graph_source_side_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (@=
      (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
      (@gray_transf_graph_source_side B C F G epsilon x y g)
      (@fapp1_fapp0 B C F x y g))
≔ @eq_refl
    (Hom C (@fapp0 B C F x) (@fapp0 B C F y))
    (@fapp1_fapp0 B C F x y g);

// The target-side projection computes to G[g].
symbol gray_transf_graph_target_side
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
≔ sigma_Fst
    (sigma_Snd
      (@gray_transf_graph_arrow B C F G epsilon x y g));

symbol gray_transf_graph_target_side_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (@=
      (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
      (@gray_transf_graph_target_side B C F G epsilon x y g)
      (@fapp1_fapp0 B C G x y g))
≔ @eq_refl
    (Hom C (@fapp0 B C G x) (@fapp0 B C G y))
    (@fapp1_fapp0 B C G x y g);

// The remaining nested-Sigma projection computes to the standard cell.
symbol gray_transf_graph_cell
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
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
          B C F G epsilon x y g)))
≔ sigma_Snd
    (sigma_Snd
      (@gray_transf_graph_arrow B C F G epsilon x y g));

symbol gray_transf_graph_cell_projection_path
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
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
          (@tapp0_fapp0 B C F G x epsilon)
          (@tapp0_fapp0 B C F G y epsilon)
          (@fapp1_fapp0 B C F x y g)
          (@fapp1_fapp0 B C G x y g)))
      (@gray_transf_graph_cell B C F G epsilon x y g)
      (@gray_transf_standard_cell B C F G epsilon x y g))
≔ @eq_refl
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
    (@gray_transf_standard_cell B C F G epsilon x y g);

// The graph is not capped at its square reading: another whole hom action is
// available for the recursive Gray-cube successor.
symbol gray_transf_graph_next_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  (x y : τ (Obj B))
  : τ (Functor
      (Hom_cat B x y)
      (Hom_cat
        (@LaxArrow_cat C)
        (@gray_transf_graph_obj B C F G epsilon x)
        (@gray_transf_graph_obj B C F G epsilon y)))
≔ @fapp1_func
    B (@LaxArrow_cat C)
    (@gray_transf_graph_func B C F G epsilon)
    x y;
