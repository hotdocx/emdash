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

  The represented-Sigma/opposite construction is retained as protected
  derivation evidence.  The public stable graph computes on objects and capped
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

// Source, middle, and target families for a transformation graph.
protected symbol gray_transf_graph_source_raw_catd
  [B : Cat]
  : τ (Catd (Op_cat B))
≔ @homdc_edge_catd
    B B (@hom_int B B (@id_func B));

protected symbol gray_transf_graph_source_catd
  [B : Cat]
  : τ (Catd (Op_cat B))
≔ @hom_identity_graph_catd B;

protected symbol gray_transf_graph_middle_inner_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functor (Op_cat B) (@Catd_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (Op_cat C)
    (@Catd_cat B)
    (@hom_int C B G)
    (@Op_func B C F);

protected symbol gray_transf_graph_middle_raw_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (@Catd_cat B)
    Cat_cat
    (@Sigma_func B)
    (@gray_transf_graph_middle_inner_catd B C F G);

protected symbol gray_transf_graph_middle_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @Op_catd
    (Op_cat B)
    (@gray_transf_graph_middle_raw_catd B C F G);

protected symbol gray_transf_graph_target_base_catd
  [C : Cat]
  : τ (Catd (Op_cat C))
≔ @homdc_op_edge_catd
    C C (@hom_int C C (@id_func C));

protected symbol gray_transf_graph_target_catd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @Pullback_catd
    (Op_cat B)
    (Op_cat C)
    (@gray_transf_graph_target_base_catd C)
    (@Op_func B C F);

// Fibrewise Sigma of the existing whole internal action.
protected symbol gray_transf_graph_sigma_transf
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  : τ (Transf
      (@gray_transf_graph_source_raw_catd B)
      (@gray_transf_graph_middle_raw_catd B C F G))
≔ @fapp0
    (@Transf_cat
      (Op_cat B)
      (@Catd_cat B)
      (@hom_int B B (@id_func B))
      (@gray_transf_graph_middle_inner_catd B C F G))
    (@Transf_cat
      (Op_cat B)
      Cat_cat
      (@gray_transf_graph_source_raw_catd B)
      (@gray_transf_graph_middle_raw_catd B C F G))
    (@comp_cat_cov_fapp1_func
      (Op_cat B)
      (@Catd_cat B)
      Cat_cat
      (@Sigma_func B)
      (@hom_int B B (@id_func B))
      (@gray_transf_graph_middle_inner_catd B C F G))
    (@tapp1_int_fapp0_transf B C F G epsilon);

// Pointwise opposite turns that whole transformation into the displayed map
// used by the variance-correct lax-arrow total.
protected symbol gray_transf_graph_sigma_op_funcd
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  : τ (Functord
      (@gray_transf_graph_source_catd B)
      (@gray_transf_graph_middle_catd B C F G))
≔ @Op_funcd
    (Op_cat B)
    (@gray_transf_graph_source_raw_catd B)
    (@gray_transf_graph_middle_raw_catd B C F G)
    (@gray_transf_graph_sigma_transf B C F G epsilon);

protected symbol gray_transf_graph_identity_sec
  [B : Cat]
  : τ (Obj (@Pi_cat (Op_cat B) (@gray_transf_graph_source_catd B)))
≔ @hom_identity_graph_sec B;

protected symbol gray_transf_graph_middle_sec
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  : τ (Obj (@Pi_cat
      (Op_cat B)
      (@gray_transf_graph_middle_catd B C F G)))
≔ @section_postcomp_sec
    (Op_cat B)
    (@gray_transf_graph_source_catd B)
    (@gray_transf_graph_middle_catd B C F G)
    (@gray_transf_graph_sigma_op_funcd B C F G epsilon)
    (@gray_transf_graph_identity_sec B);

// The represented C-family at the varying source F[x].
protected symbol gray_transf_graph_rep_catd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Functor (Op_cat B) (@Catd_cat C))
≔ @comp_cat_fapp0
    (Op_cat B)
    (Op_cat C)
    (@Catd_cat C)
    (@hom_int C C (@id_func C))
    (@Op_func B C F);

// The two family-valued endpoints of total base change by G.
protected symbol gray_transf_graph_basechange_source_func
  [B C : Cat]
  (G : τ (Functor B C))
  : τ (Functor (@Catd_cat C) Cat_cat)
≔ @comp_cat_fapp0
    (@Catd_cat C)
    (@Catd_cat B)
    Cat_cat
    (@Sigma_func B)
    (@Pullback_catd_func B C G);

protected symbol gray_transf_graph_basechange_source_catd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (@Catd_cat C)
    Cat_cat
    (@gray_transf_graph_basechange_source_func B C G)
    (@gray_transf_graph_rep_catd B C F);

protected symbol gray_transf_graph_target_raw_catd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Catd (Op_cat B))
≔ @comp_cat_fapp0
    (Op_cat B)
    (Op_cat C)
    Cat_cat
    (@homdc_edge_catd C C (@hom_int C C (@id_func C)))
    (@Op_func B C F);

// Precompose the family-natural total-base-change transformation by the
// represented family x |-> Hom_C(F[x],-).
protected symbol gray_transf_graph_basechange_transf
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Transf
      (@gray_transf_graph_basechange_source_catd B C F G)
      (@gray_transf_graph_target_raw_catd B C F))
≔ @fapp0
    (@Transf_cat
      (@Catd_cat C)
      Cat_cat
      (@gray_transf_graph_basechange_source_func B C G)
      (@Sigma_func C))
    (@Transf_cat
      (Op_cat B)
      Cat_cat
      (@gray_transf_graph_basechange_source_catd B C F G)
      (@gray_transf_graph_target_raw_catd B C F))
    (@comp_cat_con_fapp1_func
      (Op_cat B)
      (@Catd_cat C)
      Cat_cat
      (@gray_transf_graph_rep_catd B C F)
      (@gray_transf_graph_basechange_source_func B C G)
      (@Sigma_func C))
    (@sigma_pullback_total_transf B C G);

// Pointwise opposite of the actual base-change transformation.
protected symbol gray_transf_graph_basechange_op_raw_funcd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functord
      (@Op_catd
        (Op_cat B)
        (@gray_transf_graph_basechange_source_catd B C F G))
      (@Op_catd
        (Op_cat B)
        (@gray_transf_graph_target_raw_catd B C F)))
≔ @Op_funcd
    (Op_cat B)
    (@gray_transf_graph_basechange_source_catd B C F G)
    (@gray_transf_graph_target_raw_catd B C F)
    (@gray_transf_graph_basechange_transf B C F G);

protected symbol gray_transf_graph_basechange_source_reframe_funcd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functord
      (@gray_transf_graph_middle_catd B C F G)
      (@Op_catd
        (Op_cat B)
        (@gray_transf_graph_basechange_source_catd B C F G)))
≔ @id_funcd
    (Op_cat B)
    (@gray_transf_graph_middle_catd B C F G);

protected symbol gray_transf_graph_basechange_target_reframe_funcd
  [B C : Cat]
  (F : τ (Functor B C))
  : τ (Functord
      (@Op_catd
        (Op_cat B)
        (@gray_transf_graph_target_raw_catd B C F))
      (@gray_transf_graph_target_catd B C F))
≔ @id_funcd
    (Op_cat B)
    (@Op_catd
      (Op_cat B)
      (@gray_transf_graph_target_raw_catd B C F));

protected symbol gray_transf_graph_basechange_op_funcd
  [B C : Cat]
  (F G : τ (Functor B C))
  : τ (Functord
      (@gray_transf_graph_middle_catd B C F G)
      (@gray_transf_graph_target_catd B C F))
≔ @comp_catd_fapp0
    (Op_cat B)
    (@gray_transf_graph_middle_catd B C F G)
    (@Op_catd
      (Op_cat B)
      (@gray_transf_graph_target_raw_catd B C F))
    (@gray_transf_graph_target_catd B C F)
    (@gray_transf_graph_basechange_target_reframe_funcd B C F)
    (@comp_catd_fapp0
      (Op_cat B)
      (@gray_transf_graph_middle_catd B C F G)
      (@Op_catd
        (Op_cat B)
        (@gray_transf_graph_basechange_source_catd B C F G))
      (@Op_catd
        (Op_cat B)
        (@gray_transf_graph_target_raw_catd B C F))
      (@gray_transf_graph_basechange_op_raw_funcd B C F G)
      (@gray_transf_graph_basechange_source_reframe_funcd B C F G));

protected symbol gray_transf_graph_target_sec
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  : τ (Obj (@Pi_cat
      (Op_cat B)
      (@gray_transf_graph_target_catd B C F)))
≔ @section_postcomp_sec
    (Op_cat B)
    (@gray_transf_graph_middle_catd B C F G)
    (@gray_transf_graph_target_catd B C F)
    (@gray_transf_graph_basechange_op_funcd B C F G)
    (@gray_transf_graph_middle_sec B C F G epsilon);

// Totalize the section, move its outer base along F^op, then take opposites.
protected symbol gray_transf_graph_underlying_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  : τ (Functor
      (Op_cat B)
      (@Sigma_cat
        (Op_cat C)
        (@gray_transf_graph_target_base_catd C)))
≔ @comp_cat_fapp0
    (Op_cat B)
    (@Sigma_cat
      (Op_cat B)
      (@gray_transf_graph_target_catd B C F))
    (@Sigma_cat
      (Op_cat C)
      (@gray_transf_graph_target_base_catd C))
    (@sigma_pullback_total_func
      (Op_cat B)
      (Op_cat C)
      (@Op_func B C F)
      (@gray_transf_graph_target_base_catd C))
    (@section_total_func
      (Op_cat B)
      (@gray_transf_graph_target_catd B C F)
      (@gray_transf_graph_target_sec B C F G epsilon));

// Protected transparent derivation retained for architecture evidence.
protected symbol gray_transf_graph_internal_func
  [B C : Cat]
  [F G : τ (Functor B C)]
  (epsilon : τ (Transf F G))
  : τ (Functor B (@LaxArrow_cat C))
≔ @Op_func
    (Op_cat B)
    (@Sigma_cat
      (Op_cat C)
      (@gray_transf_graph_target_base_catd C))
    (@gray_transf_graph_underlying_func B C F G epsilon);

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
