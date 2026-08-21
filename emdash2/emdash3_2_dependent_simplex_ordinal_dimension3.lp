/*
  Constructive ordinal dependent simplex in dimension three.

  The standard Delta[3] is the join Delta[2] * 1.  The existing shaped beta
  compares the cross observed from the identity join extension with its
  primitive cross.  Fixing vertex zero turns that comparison into equality of
  whole PathOut maps.  The generic post/left internal action on the two
  successive Delta[2] triangle cells supplies the tetrahedral top cell.

  Its source is related to represented transport by first-class paths through
  the stable identity/general postcomposition owners and the cold whole
  Cat-precomposition comparison.  Pairing that cell with face 023 constructs
  one native `DependentSimplex3_cat` object.  Mapping this single source by
  `dependent_simplex3_map(H)` gives the observation for arbitrary H.

  No opaque filler, endpoint rewrite, Sigma eta, runtime rule, or proof-time
  unifier is introduced.
*/

require open emdash.emdash3_2_dependent_simplex_ordinal_filler;
require open emdash.emdash3_2_shaped_pathout;
require open emdash.emdash3_2_dependent_simplex_faces;

// Standard source and target ordinal shapes Delta[2] and Delta[3].
symbol ordinal_simplex3_source_cat : Cat
≔ @DirectedSimplex_cat (succ (succ zero));

symbol ordinal_simplex3_target_cat : Cat
≔ @DirectedSimplex_cat (succ (succ (succ zero)));

symbol ordinal_simplex3_source_id
  : τ (Functor ordinal_simplex3_source_cat ordinal_simplex3_source_cat)
≔ @id_func ordinal_simplex3_source_cat;

// The three old vertices and their selected edges.
symbol ordinal_simplex3_x0 : τ (Obj ordinal_simplex3_source_cat)
≔ @ordinal_simplex1_source
    ordinal_simplex3_source_cat simplex_edge_zero_one_func;

symbol ordinal_simplex3_x1 : τ (Obj ordinal_simplex3_source_cat)
≔ @ordinal_simplex1_target
    ordinal_simplex3_source_cat simplex_edge_zero_one_func;

symbol ordinal_simplex3_x2 : τ (Obj ordinal_simplex3_source_cat)
≔ @ordinal_simplex1_target
    ordinal_simplex3_source_cat simplex_edge_zero_two_func;

symbol ordinal_simplex3_p01
  : τ (Hom ordinal_simplex3_source_cat
      ordinal_simplex3_x0 ordinal_simplex3_x1)
≔ @ordinal_simplex1_arrow
    ordinal_simplex3_source_cat simplex_edge_zero_one_func;

symbol ordinal_simplex3_dimension2_compatibility
  : τ (@OrdinalDependentSimplex2Compatibility
      ordinal_simplex3_source_cat ordinal_simplex3_source_id)
≔ @ordinal_dependent_simplex2_compatibility
    ordinal_simplex3_source_cat ordinal_simplex3_source_id;

symbol ordinal_simplex3_p02
  : τ (Hom ordinal_simplex3_source_cat
      ordinal_simplex3_x0 ordinal_simplex3_x2)
≔ @ordinal_simplex2_edge02_normalized
    ordinal_simplex3_source_cat ordinal_simplex3_source_id
    ordinal_simplex3_dimension2_compatibility;

symbol ordinal_simplex3_p12
  : τ (Hom ordinal_simplex3_source_cat
      ordinal_simplex3_x1 ordinal_simplex3_x2)
≔ @ordinal_simplex2_edge12_normalized
    ordinal_simplex3_source_cat ordinal_simplex3_source_id
    ordinal_simplex3_dimension2_compatibility;

// Stable represented composite and literal raw composite of 01 then 12.
symbol ordinal_simplex3_p012_stable
  : τ (Hom ordinal_simplex3_source_cat
      ordinal_simplex3_x0 ordinal_simplex3_x2)
≔ @hom_postcomp_fapp0
    ordinal_simplex3_source_cat ordinal_simplex3_source_cat
    ordinal_simplex3_source_id
    ordinal_simplex3_x0 ordinal_simplex3_x1 ordinal_simplex3_x2
    ordinal_simplex3_p12 ordinal_simplex3_p01;

symbol ordinal_simplex3_p012_raw
  : τ (Hom ordinal_simplex3_source_cat
      ordinal_simplex3_x0 ordinal_simplex3_x2)
≔ @comp_fapp0
    ordinal_simplex3_source_cat
    ordinal_simplex3_x0 ordinal_simplex3_x1 ordinal_simplex3_x2
    ordinal_simplex3_p12 ordinal_simplex3_p01;

symbol ordinal_simplex3_p012_stable_raw_path
  : τ (@=
      (Hom ordinal_simplex3_source_cat
        ordinal_simplex3_x0 ordinal_simplex3_x2)
      ordinal_simplex3_p012_stable ordinal_simplex3_p012_raw)
≔ @path_pseudo_laxity_postcomp_comp_path
    ordinal_simplex3_source_cat ordinal_simplex3_source_cat
    ordinal_simplex3_source_id
    ordinal_simplex3_x0 ordinal_simplex3_x1 ordinal_simplex3_x2
    ordinal_simplex3_p12 ordinal_simplex3_p01;

// The two successive outgoing-path arrows: raw -> stable -> direct.
symbol ordinal_simplex3_raw_stable_cell
  : τ (Hom
      (Hom_cat ordinal_simplex3_source_cat
        ordinal_simplex3_x0 ordinal_simplex3_x2)
      ordinal_simplex3_p012_raw ordinal_simplex3_p012_stable)
≔ @path_to_hom
    (Hom_cat ordinal_simplex3_source_cat
      ordinal_simplex3_x0 ordinal_simplex3_x2)
    ordinal_simplex3_p012_raw ordinal_simplex3_p012_stable
    (@eq_sym
      (Hom ordinal_simplex3_source_cat
        ordinal_simplex3_x0 ordinal_simplex3_x2)
      ordinal_simplex3_p012_stable ordinal_simplex3_p012_raw
      ordinal_simplex3_p012_stable_raw_path);

symbol ordinal_simplex3_stable_direct_cell
  : τ (Hom
      (Hom_cat ordinal_simplex3_source_cat
        ordinal_simplex3_x0 ordinal_simplex3_x2)
      ordinal_simplex3_p012_stable ordinal_simplex3_p02)
≔ ordinal_simplex2_source_canonical_filler;

// Identity join data presenting Delta[3] = Delta[2] * 1.
symbol ordinal_simplex3_left
  : τ (Functor ordinal_simplex3_source_cat ordinal_simplex3_target_cat)
≔ @join_fst_func ordinal_simplex3_source_cat Terminal_cat;

symbol ordinal_simplex3_right
  : τ (Functor Terminal_cat ordinal_simplex3_target_cat)
≔ @join_map_right_func
    ordinal_simplex3_source_cat Terminal_cat
    ordinal_simplex3_source_cat Terminal_cat
    profiled_terminal;

symbol ordinal_simplex3_source_cross
  : τ (Obj (@Prof_transf_cat
      ordinal_simplex3_target_cat
      ordinal_simplex3_source_cat
      ordinal_simplex3_target_cat Terminal_cat
      (@Terminal_prof ordinal_simplex3_source_cat Terminal_cat)
      ordinal_simplex3_left
      (@Unit_prof ordinal_simplex3_target_cat)
      ordinal_simplex3_right))
≔ @join_map_cross_transf
    ordinal_simplex3_source_cat Terminal_cat
    ordinal_simplex3_source_cat Terminal_cat
    ordinal_simplex3_source_id profiled_terminal;

symbol ordinal_simplex3_join_data
  : τ (@JoinMapObjectData
      ordinal_simplex3_source_cat Terminal_cat ordinal_simplex3_target_cat)
≔ @Struct_sigma
    (Functor ordinal_simplex3_source_cat ordinal_simplex3_target_cat)
    (λ first : τ (Functor
        ordinal_simplex3_source_cat ordinal_simplex3_target_cat),
      @Σ_
        (Functor Terminal_cat ordinal_simplex3_target_cat)
        (λ second : τ (Functor Terminal_cat ordinal_simplex3_target_cat),
          Obj (@Prof_transf_cat
            ordinal_simplex3_target_cat
            ordinal_simplex3_source_cat
            ordinal_simplex3_target_cat Terminal_cat
            (@Terminal_prof ordinal_simplex3_source_cat Terminal_cat)
            first (@Unit_prof ordinal_simplex3_target_cat) second)))
    ordinal_simplex3_left
    (@Struct_sigma
      (Functor Terminal_cat ordinal_simplex3_target_cat)
      (λ second : τ (Functor Terminal_cat ordinal_simplex3_target_cat),
        Obj (@Prof_transf_cat
          ordinal_simplex3_target_cat
          ordinal_simplex3_source_cat
          ordinal_simplex3_target_cat Terminal_cat
          (@Terminal_prof ordinal_simplex3_source_cat Terminal_cat)
          ordinal_simplex3_left
          (@Unit_prof ordinal_simplex3_target_cat) second))
      ordinal_simplex3_right ordinal_simplex3_source_cross);

// Shape the whole join cross over the old Delta[2] parameter.
symbol ordinal_simplex3_shape_left
  : τ (Functor ordinal_simplex3_source_cat ordinal_simplex3_source_cat)
≔ ordinal_simplex3_source_id;

symbol ordinal_simplex3_shape_right
  : τ (Functor ordinal_simplex3_source_cat Terminal_cat)
≔ @Const_func ordinal_simplex3_source_cat Terminal_cat Terminal_obj;

symbol ordinal_simplex3_beta_left
  : τ (Functor ordinal_simplex3_source_cat ordinal_simplex3_target_cat)
≔ @comp_cat_fapp0
    ordinal_simplex3_source_cat ordinal_simplex3_source_cat
    ordinal_simplex3_target_cat
    (@join_map_object_left
      ordinal_simplex3_source_cat Terminal_cat
      ordinal_simplex3_target_cat ordinal_simplex3_join_data)
    ordinal_simplex3_shape_left;

symbol ordinal_simplex3_beta_right
  : τ (Functor ordinal_simplex3_source_cat ordinal_simplex3_target_cat)
≔ @comp_cat_fapp0
    ordinal_simplex3_source_cat Terminal_cat ordinal_simplex3_target_cat
    (@join_map_object_right
      ordinal_simplex3_source_cat Terminal_cat
      ordinal_simplex3_target_cat ordinal_simplex3_join_data)
    ordinal_simplex3_shape_right;

symbol ordinal_simplex3_observed_cone
  : τ (@Prof_hom
      ordinal_simplex3_source_cat
      ordinal_simplex3_target_cat ordinal_simplex3_target_cat
      ordinal_simplex3_beta_left
      (@Unit_prof ordinal_simplex3_target_cat)
      ordinal_simplex3_beta_right)
≔ @join_map_observe_cross_at
    ordinal_simplex3_source_cat Terminal_cat
    ordinal_simplex3_target_cat ordinal_simplex3_source_cat
    (@join_map_extend_object
      ordinal_simplex3_source_cat Terminal_cat
      ordinal_simplex3_target_cat ordinal_simplex3_join_data)
    ordinal_simplex3_shape_left ordinal_simplex3_shape_right;

symbol ordinal_simplex3_primitive_cone
  : τ (@Prof_hom
      ordinal_simplex3_source_cat
      ordinal_simplex3_target_cat ordinal_simplex3_target_cat
      ordinal_simplex3_beta_left
      (@Unit_prof ordinal_simplex3_target_cat)
      ordinal_simplex3_beta_right)
≔ @Prof_cell_eval
    ordinal_simplex3_source_cat
    ordinal_simplex3_source_cat Terminal_cat
    ordinal_simplex3_target_cat ordinal_simplex3_target_cat
    (@Unit_prof ordinal_simplex3_target_cat)
    (@join_map_object_left
      ordinal_simplex3_source_cat Terminal_cat
      ordinal_simplex3_target_cat ordinal_simplex3_join_data)
    (@join_map_object_right
      ordinal_simplex3_source_cat Terminal_cat
      ordinal_simplex3_target_cat ordinal_simplex3_join_data)
    ordinal_simplex3_shape_left ordinal_simplex3_shape_right
    (@join_map_extend_cross
      ordinal_simplex3_source_cat Terminal_cat
      ordinal_simplex3_target_cat ordinal_simplex3_join_data);

symbol ordinal_simplex3_cone_path
  : τ (@=
      (@Prof_hom
        ordinal_simplex3_source_cat
        ordinal_simplex3_target_cat ordinal_simplex3_target_cat
        ordinal_simplex3_beta_left
        (@Unit_prof ordinal_simplex3_target_cat)
        ordinal_simplex3_beta_right)
      ordinal_simplex3_observed_cone ordinal_simplex3_primitive_cone)
≔ @join_map_extend_cross_shaped_beta
    ordinal_simplex3_source_cat Terminal_cat
    ordinal_simplex3_target_cat ordinal_simplex3_source_cat
    ordinal_simplex3_join_data
    ordinal_simplex3_shape_left ordinal_simplex3_shape_right;

// Whole fixed-source PathOut maps induced by the two shaped cones.
symbol ordinal_simplex3_source_pathout_cat : Cat
≔ @PathOut_cat ordinal_simplex3_source_cat ordinal_simplex3_x0;

symbol ordinal_simplex3_y0 : τ (Obj ordinal_simplex3_target_cat)
≔ @fapp0
    ordinal_simplex3_source_cat ordinal_simplex3_target_cat
    ordinal_simplex3_beta_left ordinal_simplex3_x0;

symbol ordinal_simplex3_target_pathout_cat : Cat
≔ @PathOut_cat ordinal_simplex3_target_cat ordinal_simplex3_y0;

symbol ordinal_simplex3_observed_pathout_func
  : τ (Functor
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat)
≔ @shaped_pathout_func
    ordinal_simplex3_source_cat ordinal_simplex3_target_cat
    ordinal_simplex3_beta_left ordinal_simplex3_beta_right
    ordinal_simplex3_observed_cone ordinal_simplex3_x0;

symbol ordinal_simplex3_primitive_pathout_func
  : τ (Functor
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat)
≔ @shaped_pathout_func
    ordinal_simplex3_source_cat ordinal_simplex3_target_cat
    ordinal_simplex3_beta_left ordinal_simplex3_beta_right
    ordinal_simplex3_primitive_cone ordinal_simplex3_x0;

symbol ordinal_simplex3_pathout_func_path
  : τ (@=
      (Obj (Functor_cat
        ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_target_pathout_cat))
      ordinal_simplex3_observed_pathout_func
      ordinal_simplex3_primitive_pathout_func)
≔ @eq_ap
    (@Prof_hom
      ordinal_simplex3_source_cat
      ordinal_simplex3_target_cat ordinal_simplex3_target_cat
      ordinal_simplex3_beta_left
      (@Unit_prof ordinal_simplex3_target_cat)
      ordinal_simplex3_beta_right)
    (Obj (Functor_cat
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat))
    (λ cone : τ (@Prof_hom
        ordinal_simplex3_source_cat
        ordinal_simplex3_target_cat ordinal_simplex3_target_cat
        ordinal_simplex3_beta_left
        (@Unit_prof ordinal_simplex3_target_cat)
        ordinal_simplex3_beta_right),
      @shaped_pathout_func
        ordinal_simplex3_source_cat ordinal_simplex3_target_cat
        ordinal_simplex3_beta_left ordinal_simplex3_beta_right
        cone ordinal_simplex3_x0)
    ordinal_simplex3_observed_cone ordinal_simplex3_primitive_cone
    ordinal_simplex3_cone_path;

symbol ordinal_simplex3_pathout_transf
  : τ (Transf
      ordinal_simplex3_observed_pathout_func
      ordinal_simplex3_primitive_pathout_func)
≔ @path_to_hom
    (Functor_cat
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat)
    ordinal_simplex3_observed_pathout_func
    ordinal_simplex3_primitive_pathout_func
    ordinal_simplex3_pathout_func_path;

// Three outgoing-path objects and their two successive arrows.
symbol ordinal_simplex3_raw_obj
  : τ (Obj ordinal_simplex3_source_pathout_cat)
≔ @pathout_obj
    ordinal_simplex3_source_cat ordinal_simplex3_x0
    ordinal_simplex3_x2 ordinal_simplex3_p012_raw;

symbol ordinal_simplex3_stable_obj
  : τ (Obj ordinal_simplex3_source_pathout_cat)
≔ @pathout_obj
    ordinal_simplex3_source_cat ordinal_simplex3_x0
    ordinal_simplex3_x2 ordinal_simplex3_p012_stable;

symbol ordinal_simplex3_direct_obj
  : τ (Obj ordinal_simplex3_source_pathout_cat)
≔ @pathout_obj
    ordinal_simplex3_source_cat ordinal_simplex3_x0
    ordinal_simplex3_x2 ordinal_simplex3_p02;

symbol ordinal_simplex3_raw_to_stable
  : τ (Hom ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
≔ @sigma_arrow
    ordinal_simplex3_source_cat
    (@Rep_catd ordinal_simplex3_source_cat ordinal_simplex3_x0)
    ordinal_simplex3_x2 ordinal_simplex3_x2
    ordinal_simplex3_p012_raw ordinal_simplex3_p012_stable
    (@id ordinal_simplex3_source_cat ordinal_simplex3_x2)
    ordinal_simplex3_raw_stable_cell;

symbol ordinal_simplex3_stable_to_direct
  : τ (Hom ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj)
≔ @sigma_arrow
    ordinal_simplex3_source_cat
    (@Rep_catd ordinal_simplex3_source_cat ordinal_simplex3_x0)
    ordinal_simplex3_x2 ordinal_simplex3_x2
    ordinal_simplex3_p012_stable ordinal_simplex3_p02
    (@id ordinal_simplex3_source_cat ordinal_simplex3_x2)
    ordinal_simplex3_stable_direct_cell;

// The three target edges and faces 012, 023, and 013.
symbol ordinal_simplex3_e01
  : τ (Obj (@DependentSimplex1_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0))
≔ @fapp0
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_observed_pathout_func ordinal_simplex3_raw_obj;

symbol ordinal_simplex3_e02
  : τ (Obj (@DependentSimplex1_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0))
≔ @fapp0
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_primitive_pathout_func ordinal_simplex3_stable_obj;

symbol ordinal_simplex3_e03
  : τ (Obj (@DependentSimplex1_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0))
≔ @fapp0
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_primitive_pathout_func ordinal_simplex3_direct_obj;

symbol ordinal_simplex3_face012
  : τ (Hom
      (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
      ordinal_simplex3_e01 ordinal_simplex3_e02)
≔ @tapp1_fapp0
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_observed_pathout_func
    ordinal_simplex3_primitive_pathout_func
    ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj
    ordinal_simplex3_pathout_transf ordinal_simplex3_raw_to_stable;

symbol ordinal_simplex3_face023
  : τ (Hom
      (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
      ordinal_simplex3_e02 ordinal_simplex3_e03)
≔ @fapp1_fapp0
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_primitive_pathout_func
    ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct;

// Whole post/left laxity at the second arrow, retained in the first arrow.
symbol ordinal_simplex3_top_lhs_func
  : τ (Functor
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @functord_transport_lhs_func
    ordinal_simplex3_source_pathout_cat
    (@hom_ ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_source_pathout_cat
      (@id_func ordinal_simplex3_source_pathout_cat)
      ordinal_simplex3_raw_obj)
    (@hom_ ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_primitive_pathout_func ordinal_simplex3_e01)
    (@tapp1_at_transf
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_observed_pathout_func
      ordinal_simplex3_primitive_pathout_func
      ordinal_simplex3_raw_obj ordinal_simplex3_pathout_transf)
    ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct;

symbol ordinal_simplex3_top_rhs_func
  : τ (Functor
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @functord_transport_rhs_func
    ordinal_simplex3_source_pathout_cat
    (@hom_ ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_source_pathout_cat
      (@id_func ordinal_simplex3_source_pathout_cat)
      ordinal_simplex3_raw_obj)
    (@hom_ ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_primitive_pathout_func ordinal_simplex3_e01)
    (@tapp1_at_transf
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_observed_pathout_func
      ordinal_simplex3_primitive_pathout_func
      ordinal_simplex3_raw_obj ordinal_simplex3_pathout_transf)
    ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct;

symbol ordinal_simplex3_top_source
  : τ (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @fapp0
    (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
    (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03)
    ordinal_simplex3_top_lhs_func ordinal_simplex3_raw_to_stable;

symbol ordinal_simplex3_top_target
  : τ (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @fapp0
    (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
    (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03)
    ordinal_simplex3_top_rhs_func ordinal_simplex3_raw_to_stable;

symbol ordinal_simplex3_face013
  : τ (Hom
      (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
      ordinal_simplex3_e01 ordinal_simplex3_e03)
≔ ordinal_simplex3_top_target;

symbol ordinal_simplex3_top_cell
  : τ (Hom
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)
      ordinal_simplex3_top_source ordinal_simplex3_top_target)
≔ @tapp1_post_laxity_cell
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_observed_pathout_func
    ordinal_simplex3_primitive_pathout_func
    ordinal_simplex3_pathout_transf
    ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj
    ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct ordinal_simplex3_raw_to_stable;

symbol ordinal_simplex3_face012_obj
  : τ (Obj (@DependentSimplex2_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0
      ordinal_simplex3_e01))
≔ @dependent_simplex2
    ordinal_simplex3_target_cat ordinal_simplex3_y0
    ordinal_simplex3_e01 ordinal_simplex3_e02
    ordinal_simplex3_face012;

symbol ordinal_simplex3_face013_obj
  : τ (Obj (@DependentSimplex2_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0
      ordinal_simplex3_e01))
≔ @dependent_simplex2
    ordinal_simplex3_target_cat ordinal_simplex3_y0
    ordinal_simplex3_e01 ordinal_simplex3_e03
    ordinal_simplex3_face013;

// Stable represented source expected by the native tetrahedral fibre.
symbol ordinal_simplex3_represented_source
  : τ (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @fapp0
    (Fibre_cat
      (@Rep_catd ordinal_simplex3_target_pathout_cat ordinal_simplex3_e01)
      ordinal_simplex3_e02)
    (Fibre_cat
      (@Rep_catd ordinal_simplex3_target_pathout_cat ordinal_simplex3_e01)
      ordinal_simplex3_e03)
    (@catd_transport_func
      ordinal_simplex3_target_pathout_cat
      (@Rep_catd ordinal_simplex3_target_pathout_cat ordinal_simplex3_e01)
      ordinal_simplex3_e02 ordinal_simplex3_e03 ordinal_simplex3_face023)
    ordinal_simplex3_face012;

symbol ordinal_simplex3_identity_post_source
  : τ (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @hom_postcomp_fapp0
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_target_pathout_cat
    (@id_func ordinal_simplex3_target_pathout_cat)
    ordinal_simplex3_e01 ordinal_simplex3_e02 ordinal_simplex3_e03
    ordinal_simplex3_face023 ordinal_simplex3_face012;

symbol ordinal_simplex3_general_post_source
  : τ (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @hom_postcomp_fapp0
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_primitive_pathout_func
    ordinal_simplex3_e01 ordinal_simplex3_stable_obj
    ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct ordinal_simplex3_face012;

symbol ordinal_simplex3_raw_post_source
  : τ (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @comp_fapp0
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_e01 ordinal_simplex3_e02 ordinal_simplex3_e03
    ordinal_simplex3_face023 ordinal_simplex3_face012;

symbol ordinal_simplex3_represented_identity_path
  : τ (@=
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_represented_source
      ordinal_simplex3_identity_post_source)
≔ @eq_refl
    (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
    ordinal_simplex3_represented_source;

symbol ordinal_simplex3_identity_raw_post_path
  : τ (@=
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_identity_post_source ordinal_simplex3_raw_post_source)
≔ @path_pseudo_laxity_postcomp_comp_path
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_target_pathout_cat
    (@id_func ordinal_simplex3_target_pathout_cat)
    ordinal_simplex3_e01 ordinal_simplex3_e02 ordinal_simplex3_e03
    ordinal_simplex3_face023 ordinal_simplex3_face012;

symbol ordinal_simplex3_general_raw_post_path
  : τ (@=
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_general_post_source ordinal_simplex3_raw_post_source)
≔ @path_pseudo_laxity_postcomp_comp_path
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_primitive_pathout_func
    ordinal_simplex3_e01 ordinal_simplex3_stable_obj
    ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct ordinal_simplex3_face012;

symbol ordinal_simplex3_identity_general_post_path
  : τ (@=
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_identity_post_source
      ordinal_simplex3_general_post_source)
≔ @eq_trans
    (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
    ordinal_simplex3_identity_post_source ordinal_simplex3_raw_post_source
    ordinal_simplex3_general_post_source
    ordinal_simplex3_identity_raw_post_path
    (@eq_sym
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_general_post_source ordinal_simplex3_raw_post_source
      ordinal_simplex3_general_raw_post_path);

// Whole left transport telescope and its projection to the capped owner.
symbol ordinal_simplex3_lhs_tele_func
  : τ (Functor
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj)
      (Functor_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)))
≔ @functord_transport_lhs_tele_func
    ordinal_simplex3_source_pathout_cat
    (@hom_ ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_source_pathout_cat
      (@id_func ordinal_simplex3_source_pathout_cat)
      ordinal_simplex3_raw_obj)
    (@hom_ ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_primitive_pathout_func ordinal_simplex3_e01)
    (@tapp1_at_transf
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_observed_pathout_func
      ordinal_simplex3_primitive_pathout_func
      ordinal_simplex3_raw_obj ordinal_simplex3_pathout_transf)
    ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj;

symbol ordinal_simplex3_lhs_tele_at_second
  : τ (Functor
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @fapp0
    (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj)
    (Functor_cat
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
    ordinal_simplex3_lhs_tele_func ordinal_simplex3_stable_to_direct;

symbol ordinal_simplex3_lhs_tele_source
  : τ (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @fapp0
    (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
    (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03)
    ordinal_simplex3_lhs_tele_at_second ordinal_simplex3_raw_to_stable;

symbol ordinal_simplex3_transport_at_second
  : τ (Functor
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
≔ @functord_transport_func
    ordinal_simplex3_source_pathout_cat
    (@hom_ ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_source_pathout_cat
      (@id_func ordinal_simplex3_source_pathout_cat)
      ordinal_simplex3_raw_obj)
    (@hom_ ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_primitive_pathout_func ordinal_simplex3_e01)
    (@tapp1_at_transf
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_observed_pathout_func
      ordinal_simplex3_primitive_pathout_func
      ordinal_simplex3_raw_obj ordinal_simplex3_pathout_transf)
    ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct;

symbol ordinal_simplex3_lhs_tele_transport_path
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)))
      ordinal_simplex3_lhs_tele_at_second
      ordinal_simplex3_transport_at_second)
≔ @eq_ap
    (Hom Cat_cat
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj)
      (Functor_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)))
    (Obj (Functor_cat
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)))
    (λ H : τ (Hom Cat_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj)
        (Functor_cat
          (Hom_cat ordinal_simplex3_source_pathout_cat
            ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
          (Hom_cat ordinal_simplex3_target_pathout_cat
            ordinal_simplex3_e01 ordinal_simplex3_e03))),
      @fapp0
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj)
        (Functor_cat
          (Hom_cat ordinal_simplex3_source_pathout_cat
            ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
          (Hom_cat ordinal_simplex3_target_pathout_cat
            ordinal_simplex3_e01 ordinal_simplex3_e03))
        H ordinal_simplex3_stable_to_direct)
    ordinal_simplex3_lhs_tele_func
    (@tapp1_func
      ordinal_simplex3_source_pathout_cat Cat_cat
      (@hom_ ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_source_pathout_cat
        (@id_func ordinal_simplex3_source_pathout_cat)
        ordinal_simplex3_raw_obj)
      (@hom_ ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_primitive_pathout_func ordinal_simplex3_e01)
      ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj
      (@tapp1_at_transf
        ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_observed_pathout_func
        ordinal_simplex3_primitive_pathout_func
        ordinal_simplex3_raw_obj ordinal_simplex3_pathout_transf))
    (@functord_transport_lhs_tele_agrees
      ordinal_simplex3_source_pathout_cat
      (@hom_ ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_source_pathout_cat
        (@id_func ordinal_simplex3_source_pathout_cat)
        ordinal_simplex3_raw_obj)
      (@hom_ ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_primitive_pathout_func ordinal_simplex3_e01)
      (@tapp1_at_transf
        ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_observed_pathout_func
        ordinal_simplex3_primitive_pathout_func
        ordinal_simplex3_raw_obj ordinal_simplex3_pathout_transf)
      ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj);

symbol ordinal_simplex3_lhs_transport_path
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)))
      ordinal_simplex3_top_lhs_func ordinal_simplex3_transport_at_second)
≔ @functord_transport_lhs_agrees
    ordinal_simplex3_source_pathout_cat
    (@hom_ ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_source_pathout_cat
      (@id_func ordinal_simplex3_source_pathout_cat)
      ordinal_simplex3_raw_obj)
    (@hom_ ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_primitive_pathout_func ordinal_simplex3_e01)
    (@tapp1_at_transf
      ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_observed_pathout_func
      ordinal_simplex3_primitive_pathout_func
      ordinal_simplex3_raw_obj ordinal_simplex3_pathout_transf)
    ordinal_simplex3_stable_obj ordinal_simplex3_direct_obj
    ordinal_simplex3_stable_to_direct;

symbol ordinal_simplex3_lhs_tele_lhs_path
  : τ (@=
      (Obj (Functor_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)))
      ordinal_simplex3_lhs_tele_at_second ordinal_simplex3_top_lhs_func)
≔ @eq_trans
    (Obj (Functor_cat
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)))
    ordinal_simplex3_lhs_tele_at_second
    ordinal_simplex3_transport_at_second ordinal_simplex3_top_lhs_func
    ordinal_simplex3_lhs_tele_transport_path
    (@eq_sym
      (Obj (Functor_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)))
      ordinal_simplex3_top_lhs_func ordinal_simplex3_transport_at_second
      ordinal_simplex3_lhs_transport_path);

symbol ordinal_simplex3_lhs_tele_source_path
  : τ (@=
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_lhs_tele_source ordinal_simplex3_top_source)
≔ @eq_ap
    (Obj (Functor_cat
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)))
    (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
    (λ H : τ (Obj (Functor_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03))),
      @fapp0
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)
        H ordinal_simplex3_raw_to_stable)
    ordinal_simplex3_lhs_tele_at_second ordinal_simplex3_top_lhs_func
    ordinal_simplex3_lhs_tele_lhs_path;

symbol ordinal_simplex3_general_lhs_tele_path
  : τ (@=
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_general_post_source ordinal_simplex3_lhs_tele_source)
≔ @eq_sym
    (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
    ordinal_simplex3_lhs_tele_source ordinal_simplex3_general_post_source
    (@cat_precomp_composite_component_path
      (Hom_cat ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e02)
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)
      (@tapp1_func
        ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_observed_pathout_func
        ordinal_simplex3_primitive_pathout_func
        ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj
        ordinal_simplex3_pathout_transf)
      (@hom_postcomp_func
        ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_source_pathout_cat
        ordinal_simplex3_primitive_pathout_func
        ordinal_simplex3_e01 ordinal_simplex3_stable_obj
        ordinal_simplex3_direct_obj ordinal_simplex3_stable_to_direct)
      ordinal_simplex3_raw_to_stable);

symbol ordinal_simplex3_represented_top_source_path
  : τ (@=
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_represented_source ordinal_simplex3_top_source)
≔ @eq_trans
    (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
    ordinal_simplex3_represented_source
    ordinal_simplex3_identity_post_source ordinal_simplex3_top_source
    ordinal_simplex3_represented_identity_path
    (@eq_trans
      (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03))
      ordinal_simplex3_identity_post_source
      ordinal_simplex3_general_post_source ordinal_simplex3_top_source
      ordinal_simplex3_identity_general_post_path
      (@eq_trans
        (Obj (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03))
        ordinal_simplex3_general_post_source
        ordinal_simplex3_lhs_tele_source ordinal_simplex3_top_source
        ordinal_simplex3_general_lhs_tele_path
        ordinal_simplex3_lhs_tele_source_path));

symbol ordinal_simplex3_top_source_reframe_func
  : τ (Functor
      (Hom_cat
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)
        ordinal_simplex3_top_source ordinal_simplex3_top_target)
      (Hom_cat
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)
        ordinal_simplex3_represented_source ordinal_simplex3_top_target))
≔ @hom_precomp_along_func
    (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03)
    (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03)
    (@id_func (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03))
    ordinal_simplex3_top_target
    ordinal_simplex3_represented_source ordinal_simplex3_top_source
    (@path_to_hom
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)
      ordinal_simplex3_represented_source ordinal_simplex3_top_source
      ordinal_simplex3_represented_top_source_path);

symbol ordinal_simplex3_top_cell_reframed
  : τ (Hom
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)
      ordinal_simplex3_represented_source ordinal_simplex3_top_target)
≔ @fapp0
    (Hom_cat
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)
      ordinal_simplex3_top_source ordinal_simplex3_top_target)
    (Hom_cat
      (Hom_cat ordinal_simplex3_target_pathout_cat
        ordinal_simplex3_e01 ordinal_simplex3_e03)
      ordinal_simplex3_represented_source ordinal_simplex3_top_target)
    ordinal_simplex3_top_source_reframe_func ordinal_simplex3_top_cell;

// Native tetrahedral arrow and source object.
symbol ordinal_simplex3_theta
  : τ (Hom
      (@DependentSimplex2_cat
        ordinal_simplex3_target_cat ordinal_simplex3_y0
        ordinal_simplex3_e01)
      ordinal_simplex3_face012_obj ordinal_simplex3_face013_obj)
≔ @sigma_arrow
    (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
    (@Rep_catd
      (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
      ordinal_simplex3_e01)
    ordinal_simplex3_e02 ordinal_simplex3_e03
    ordinal_simplex3_face012 ordinal_simplex3_face013
    ordinal_simplex3_face023 ordinal_simplex3_top_cell_reframed;

symbol ordinal_dependent_simplex3_source
  : τ (Obj (@DependentSimplex3_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0
      ordinal_simplex3_e01 ordinal_simplex3_face012_obj))
≔ @dependent_simplex3
    ordinal_simplex3_target_cat ordinal_simplex3_y0
    ordinal_simplex3_e01
    ordinal_simplex3_face012_obj ordinal_simplex3_face013_obj
    ordinal_simplex3_theta;

// Map the one canonical source through the existing native dimension-three
// whole action for arbitrary H : Delta[3] -> C.
symbol ordinal_dependent_simplex3_map
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Functor
      (@DependentSimplex3_cat
        ordinal_simplex3_target_cat ordinal_simplex3_y0
        ordinal_simplex3_e01 ordinal_simplex3_face012_obj)
      (@DependentSimplex3_cat
        C
        (@fapp0 ordinal_simplex3_target_cat C H ordinal_simplex3_y0)
        (@fapp0
          (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
          (@DependentSimplex1_cat C
            (@fapp0 ordinal_simplex3_target_cat C H ordinal_simplex3_y0))
          (@dependent_simplex1_map
            ordinal_simplex3_target_cat C H ordinal_simplex3_y0)
          ordinal_simplex3_e01)
        (@fapp0
          (@DependentSimplex2_cat
            ordinal_simplex3_target_cat ordinal_simplex3_y0
            ordinal_simplex3_e01)
          _
          (@dependent_simplex2_map
            ordinal_simplex3_target_cat C H
            ordinal_simplex3_y0 ordinal_simplex3_e01)
          ordinal_simplex3_face012_obj)))
≔ @dependent_simplex3_map
    ordinal_simplex3_target_cat C H
    ordinal_simplex3_y0 ordinal_simplex3_e01
    ordinal_simplex3_face012_obj;

symbol ordinal_dependent_simplex3_observation
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj (@DependentSimplex3_cat
      C
      (@fapp0 ordinal_simplex3_target_cat C H ordinal_simplex3_y0)
      (@fapp0
        (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
        (@DependentSimplex1_cat C
          (@fapp0 ordinal_simplex3_target_cat C H ordinal_simplex3_y0))
        (@dependent_simplex1_map
          ordinal_simplex3_target_cat C H ordinal_simplex3_y0)
        ordinal_simplex3_e01)
      (@fapp0
        (@DependentSimplex2_cat
          ordinal_simplex3_target_cat ordinal_simplex3_y0
          ordinal_simplex3_e01)
        _
        (@dependent_simplex2_map
          ordinal_simplex3_target_cat C H
          ordinal_simplex3_y0 ordinal_simplex3_e01)
        ordinal_simplex3_face012_obj)))
≔ @fapp0
    (@DependentSimplex3_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0
      ordinal_simplex3_e01 ordinal_simplex3_face012_obj)
    _
    (@ordinal_dependent_simplex3_map C H)
    ordinal_dependent_simplex3_source;

// Readable mapped flag data.
symbol ordinal_dependent_simplex3_y0
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj C)
≔ @fapp0 ordinal_simplex3_target_cat C H ordinal_simplex3_y0;

symbol ordinal_dependent_simplex3_e01
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj (@DependentSimplex1_cat C
      (@ordinal_dependent_simplex3_y0 C H)))
≔ @fapp0
    (@DependentSimplex1_cat ordinal_simplex3_target_cat ordinal_simplex3_y0)
    (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
    (@dependent_simplex1_map
      ordinal_simplex3_target_cat C H ordinal_simplex3_y0)
    ordinal_simplex3_e01;

// Faces 012 and 013 are the ordinary source and target surfaces.
symbol ordinal_dependent_simplex3_face012
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H)))
≔ @fapp0
    (@DependentSimplex2_cat
      ordinal_simplex3_target_cat ordinal_simplex3_y0
      ordinal_simplex3_e01)
    (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H))
    (@dependent_simplex2_map
      ordinal_simplex3_target_cat C H
      ordinal_simplex3_y0 ordinal_simplex3_e01)
    ordinal_simplex3_face012_obj;

symbol ordinal_dependent_simplex3_face013
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H)))
≔ @sigma_Fst
    (Obj (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H)))
    (λ t : τ (Obj (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex3_y0 C H)
        (@ordinal_dependent_simplex3_e01 C H))),
      Obj (Fibre_cat
        (@Rep_catd
          (@DependentSimplex2_cat
            C (@ordinal_dependent_simplex3_y0 C H)
            (@ordinal_dependent_simplex3_e01 C H))
          (@ordinal_dependent_simplex3_face012 C H))
        t))
    (@ordinal_dependent_simplex3_observation C H);

// The mapped native tetrahedral arrow from 012 to 013.
symbol ordinal_dependent_simplex3_theta
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Hom
      (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex3_y0 C H)
        (@ordinal_dependent_simplex3_e01 C H))
      (@ordinal_dependent_simplex3_face012 C H)
      (@ordinal_dependent_simplex3_face013 C H))
≔ @sigma_Snd
    (Obj (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H)))
    (λ t : τ (Obj (@DependentSimplex2_cat
        C (@ordinal_dependent_simplex3_y0 C H)
        (@ordinal_dependent_simplex3_e01 C H))),
      Obj (Fibre_cat
        (@Rep_catd
          (@DependentSimplex2_cat
            C (@ordinal_dependent_simplex3_y0 C H)
            (@ordinal_dependent_simplex3_e01 C H))
          (@ordinal_dependent_simplex3_face012 C H))
        t))
    (@ordinal_dependent_simplex3_observation C H);

// Faces 023 and 123 are the two hom actions of the doubly-fibred surface
// category. They are not independently reconstructed boundary cells.
symbol ordinal_dependent_simplex3_face023
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Hom
      (@dependent_simplex2_target_line_cat
        C (@ordinal_dependent_simplex3_y0 C H)
        (@ordinal_dependent_simplex3_e01 C H))
      (@fapp0
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_target_line_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_target_line_func
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@ordinal_dependent_simplex3_face012 C H))
      (@fapp0
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_target_line_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_target_line_func
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@ordinal_dependent_simplex3_face013 C H)))
≔ @fapp1_fapp0
    (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H))
    (@dependent_simplex2_target_line_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H))
    (@dependent_simplex2_target_line_func
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H))
    (@ordinal_dependent_simplex3_face012 C H)
    (@ordinal_dependent_simplex3_face013 C H)
    (@ordinal_dependent_simplex3_theta C H);

symbol ordinal_dependent_simplex3_face123
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Hom
      (@dependent_simplex2_base_line_cat
        C (@ordinal_dependent_simplex3_y0 C H)
        (@ordinal_dependent_simplex3_e01 C H))
      (@fapp0
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_base_line_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_base_line_func
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@ordinal_dependent_simplex3_face012 C H))
      (@fapp0
        (@DependentSimplex2_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_base_line_cat
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@dependent_simplex2_base_line_func
          C (@ordinal_dependent_simplex3_y0 C H)
          (@ordinal_dependent_simplex3_e01 C H))
        (@ordinal_dependent_simplex3_face013 C H)))
≔ @fapp1_fapp0
    (@DependentSimplex2_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H))
    (@dependent_simplex2_base_line_cat
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H))
    (@dependent_simplex2_base_line_func
      C (@ordinal_dependent_simplex3_y0 C H)
      (@ordinal_dependent_simplex3_e01 C H))
    (@ordinal_dependent_simplex3_face012 C H)
    (@ordinal_dependent_simplex3_face013 C H)
    (@ordinal_dependent_simplex3_theta C H);

// Readable endpoints inside the two surface objects.
symbol ordinal_dependent_simplex3_e02
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj (@DependentSimplex1_cat C
      (@ordinal_dependent_simplex3_y0 C H)))
≔ @sigma_Fst
    (Obj (@DependentSimplex1_cat C
      (@ordinal_dependent_simplex3_y0 C H)))
    (λ e : τ (Obj (@DependentSimplex1_cat C
        (@ordinal_dependent_simplex3_y0 C H))),
      Obj (Fibre_cat
        (@Rep_catd
          (@DependentSimplex1_cat C
            (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        e))
    (@ordinal_dependent_simplex3_face012 C H);

symbol ordinal_dependent_simplex3_e03
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj (@DependentSimplex1_cat C
      (@ordinal_dependent_simplex3_y0 C H)))
≔ @sigma_Fst
    (Obj (@DependentSimplex1_cat C
      (@ordinal_dependent_simplex3_y0 C H)))
    (λ e : τ (Obj (@DependentSimplex1_cat C
        (@ordinal_dependent_simplex3_y0 C H))),
      Obj (Fibre_cat
        (@Rep_catd
          (@DependentSimplex1_cat C
            (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        e))
    (@ordinal_dependent_simplex3_face013 C H);

symbol ordinal_dependent_simplex3_q012
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Hom
      (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
      (@ordinal_dependent_simplex3_e01 C H)
      (@ordinal_dependent_simplex3_e02 C H))
≔ @sigma_Snd
    (Obj (@DependentSimplex1_cat C
      (@ordinal_dependent_simplex3_y0 C H)))
    (λ e : τ (Obj (@DependentSimplex1_cat C
        (@ordinal_dependent_simplex3_y0 C H))),
      Obj (Fibre_cat
        (@Rep_catd
          (@DependentSimplex1_cat C
            (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        e))
    (@ordinal_dependent_simplex3_face012 C H);

symbol ordinal_dependent_simplex3_q013
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Hom
      (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
      (@ordinal_dependent_simplex3_e01 C H)
      (@ordinal_dependent_simplex3_e03 C H))
≔ @sigma_Snd
    (Obj (@DependentSimplex1_cat C
      (@ordinal_dependent_simplex3_y0 C H)))
    (λ e : τ (Obj (@DependentSimplex1_cat C
        (@ordinal_dependent_simplex3_y0 C H))),
      Obj (Fibre_cat
        (@Rep_catd
          (@DependentSimplex1_cat C
            (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        e))
    (@ordinal_dependent_simplex3_face013 C H);

symbol ordinal_dependent_simplex3_theta_base
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Hom
      (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
      (@ordinal_dependent_simplex3_e02 C H)
      (@ordinal_dependent_simplex3_e03 C H))
≔ @sigma_Fst
    (Obj (Op_cat (Hom_cat
      (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
      (@ordinal_dependent_simplex3_e02 C H)
      (@ordinal_dependent_simplex3_e03 C H))))
    (λ q : τ (Obj (Op_cat (Hom_cat
        (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
        (@ordinal_dependent_simplex3_e02 C H)
        (@ordinal_dependent_simplex3_e03 C H)))),
      Obj (Fibre_cat
        (@homd_
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@Rep_catd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@ordinal_dependent_simplex3_e01 C H))
          (@Rep_catd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@ordinal_dependent_simplex3_e01 C H))
          (@id_funcd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@Rep_catd
              (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
              (@ordinal_dependent_simplex3_e01 C H)))
          (@ordinal_dependent_simplex3_e02 C H)
          (@ordinal_dependent_simplex3_q012 C H)
          (@ordinal_dependent_simplex3_e03 C H)
          (@ordinal_dependent_simplex3_q013 C H))
        q))
    (@ordinal_dependent_simplex3_theta C H);

// The genuine dependent top component over face 023.
symbol ordinal_dependent_simplex3_top_component
  [C : Cat]
  (H : τ (Functor ordinal_simplex3_target_cat C))
  : τ (Obj (Fibre_cat
      (@homd_
        (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
        (@Rep_catd
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        (@Rep_catd
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@ordinal_dependent_simplex3_e01 C H))
        (@id_funcd
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@Rep_catd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@ordinal_dependent_simplex3_e01 C H)))
        (@ordinal_dependent_simplex3_e02 C H)
        (@ordinal_dependent_simplex3_q012 C H)
        (@ordinal_dependent_simplex3_e03 C H)
        (@ordinal_dependent_simplex3_q013 C H))
      (@ordinal_dependent_simplex3_theta_base C H)))
≔ @sigma_Snd
    (Obj (Op_cat (Hom_cat
      (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
      (@ordinal_dependent_simplex3_e02 C H)
      (@ordinal_dependent_simplex3_e03 C H))))
    (λ q : τ (Obj (Op_cat (Hom_cat
        (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
        (@ordinal_dependent_simplex3_e02 C H)
        (@ordinal_dependent_simplex3_e03 C H)))),
      Obj (Fibre_cat
        (@homd_
          (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
          (@Rep_catd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@ordinal_dependent_simplex3_e01 C H))
          (@Rep_catd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@ordinal_dependent_simplex3_e01 C H))
          (@id_funcd
            (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
            (@Rep_catd
              (@DependentSimplex1_cat C (@ordinal_dependent_simplex3_y0 C H))
              (@ordinal_dependent_simplex3_e01 C H)))
          (@ordinal_dependent_simplex3_e02 C H)
          (@ordinal_dependent_simplex3_q012 C H)
          (@ordinal_dependent_simplex3_e03 C H)
          (@ordinal_dependent_simplex3_q013 C H))
        q))
    (@ordinal_dependent_simplex3_theta C H);

// The whole laxity transformation is retained for the dimension-four child.
symbol ordinal_simplex3_top_whole
  : τ (Transf ordinal_simplex3_top_lhs_func ordinal_simplex3_top_rhs_func)
≔ @tapp1_post_laxity_transf
    ordinal_simplex3_source_pathout_cat
    ordinal_simplex3_target_pathout_cat
    ordinal_simplex3_observed_pathout_func
    ordinal_simplex3_primitive_pathout_func
    ordinal_simplex3_pathout_transf
    ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj
    ordinal_simplex3_direct_obj ordinal_simplex3_stable_to_direct;

symbol ordinal_simplex3_top_next_action
  (u v : τ (Obj (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)))
  : τ (Functor
      (Hom_cat
        (Hom_cat ordinal_simplex3_source_pathout_cat
          ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
        u v)
      (Hom_cat
        (Hom_cat ordinal_simplex3_target_pathout_cat
          ordinal_simplex3_e01 ordinal_simplex3_e03)
        (@fapp0
          (Hom_cat ordinal_simplex3_source_pathout_cat
            ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
          (Hom_cat ordinal_simplex3_target_pathout_cat
            ordinal_simplex3_e01 ordinal_simplex3_e03)
          ordinal_simplex3_top_lhs_func u)
        (@fapp0
          (Hom_cat ordinal_simplex3_source_pathout_cat
            ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
          (Hom_cat ordinal_simplex3_target_pathout_cat
            ordinal_simplex3_e01 ordinal_simplex3_e03)
          ordinal_simplex3_top_rhs_func v)))
≔ @tapp1_func
    (Hom_cat ordinal_simplex3_source_pathout_cat
      ordinal_simplex3_raw_obj ordinal_simplex3_stable_obj)
    (Hom_cat ordinal_simplex3_target_pathout_cat
      ordinal_simplex3_e01 ordinal_simplex3_e03)
    ordinal_simplex3_top_lhs_func ordinal_simplex3_top_rhs_func
    u v ordinal_simplex3_top_whole;
