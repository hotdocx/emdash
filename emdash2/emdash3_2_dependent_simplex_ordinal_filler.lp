/*
  Canonical ordinal two-simplex filler from the profiled source join cross.

  The source cross is reindexed by the same strict terminal profile used by
  the selected 02 and 12 faces. Its naturality along the opposite walking
  generator is therefore the intrinsic dependent triangle. Whole reindex and
  join-generator comparisons identify the two cross components with the
  selected edge generators; equality-induced arrows conjugate only these
  readable endpoints.

  The resulting source filler is packaged as the existing native dimension-two
  simplex. Applying dependent_simplex2_map to that single source object and
  projecting its top component constructs the filler for every ordinal triangle
  H. Thus the construction retains the Hom/Sigma/homd action and another hom
  action; it is not an opaque filler or a second simplex record. No rewrite,
  proof-time unifier, join eta, or higher-dimensional adequacy claim is added.
*/

require open emdash.emdash3_2_join_generator_compatibility;
require open emdash.emdash3_2_dependent_simplex_ordinal_adequacy;


// The exact strict-profile endpoint maps used by the selected 02 and 12 edges.
symbol profiled_vertex0
  : τ (Functor Terminal_cat WalkingArrow_cat)
≔ @strict_functor_carrier
    Terminal_cat WalkingArrow_cat
    (@selected_face_data
      zero (succ zero) simplex_vertex_zero_realization);

symbol profiled_vertex1
  : τ (Functor Terminal_cat WalkingArrow_cat)
≔ @strict_functor_carrier
    Terminal_cat WalkingArrow_cat
    (@selected_face_data
      zero (succ zero) simplex_vertex_one_realization);

symbol profiled_terminal
  : τ (Functor Terminal_cat Terminal_cat)
≔ @strict_functor_carrier
    Terminal_cat Terminal_cat
    (@strict_identity_data Terminal_cat);

// Reindex the target join's whole cross along id on the old edge and the same
// strict terminal profile used by the selected new edges.
symbol profiled_source_cross
  : τ (Obj
      (@Prof_transf_cat
        (@DirectedSimplex_cat (succ (succ zero)))
        WalkingArrow_cat
        (@DirectedSimplex_cat (succ (succ zero)))
        Terminal_cat
        (@Terminal_prof WalkingArrow_cat Terminal_cat)
        (@join_map_left_func
          WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
          (@id_func WalkingArrow_cat))
        (@Unit_prof (@DirectedSimplex_cat (succ (succ zero))))
        (@join_map_right_func
          WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
          profiled_terminal)))
≔ @join_map_cross_transf
    WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
    (@id_func WalkingArrow_cat)
    profiled_terminal;

symbol profiled_source_prof
  : τ (Catd (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat))
≔ @Prof_reindex
    (@DirectedSimplex_cat (succ (succ zero)))
    WalkingArrow_cat
    (@DirectedSimplex_cat (succ (succ zero)))
    Terminal_cat
    (@Unit_prof (@DirectedSimplex_cat (succ (succ zero))))
    (@join_map_left_func
      WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
      (@id_func WalkingArrow_cat))
    (@join_map_right_func
      WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
      profiled_terminal);

symbol profiled_base02
  : τ (Obj (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat))
≔ @Product_pair
    (Op_cat WalkingArrow_cat) Terminal_cat
    walking_arrow_src Terminal_obj;

symbol profiled_base12
  : τ (Obj (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat))
≔ @Product_pair
    (Op_cat WalkingArrow_cat) Terminal_cat
    walking_arrow_tgt Terminal_obj;

symbol profiled_cross02_func
  : τ (Functor
      Terminal_cat
      (Fibre_cat profiled_source_prof profiled_base02))
≔ @Fibre_func
    (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat)
    (@Terminal_prof WalkingArrow_cat Terminal_cat)
    profiled_source_prof
    profiled_source_cross
    profiled_base02;

symbol profiled_cross12_func
  : τ (Functor
      Terminal_cat
      (Fibre_cat profiled_source_prof profiled_base12))
≔ @Fibre_func
    (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat)
    (@Terminal_prof WalkingArrow_cat Terminal_cat)
    profiled_source_prof
    profiled_source_cross
    profiled_base12;

// Component computation of the profunctor reindex, still whole in Terminal.
symbol profiled_cross02_reindex_path
  : τ (@=
      (Obj (Functor_cat
        Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base02)))
      profiled_cross02_func
      (@join_map_source_generator_func
        WalkingArrow_cat Terminal_cat
        profiled_vertex0 profiled_terminal))
≔ @prof_reindex_transf_component_path
    WalkingArrow_cat WalkingArrow_cat
    Terminal_cat Terminal_cat
    (@Terminal_prof WalkingArrow_cat Terminal_cat)
    (@Prof_reindex
      (@DirectedSimplex_cat (succ (succ zero)))
      WalkingArrow_cat
      (@DirectedSimplex_cat (succ (succ zero)))
      Terminal_cat
      (@Unit_prof (@DirectedSimplex_cat (succ (succ zero))))
      (@join_fst_func WalkingArrow_cat Terminal_cat)
      (@join_snd_func WalkingArrow_cat Terminal_cat))
    (@join_cross_transf WalkingArrow_cat Terminal_cat)
    (@id_func WalkingArrow_cat)
    profiled_terminal
    walking_arrow_src Terminal_obj;

symbol profiled_cross12_reindex_path
  : τ (@=
      (Obj (Functor_cat
        Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base12)))
      profiled_cross12_func
      (@join_map_source_generator_func
        WalkingArrow_cat Terminal_cat
        profiled_vertex1 profiled_terminal))
≔ @prof_reindex_transf_component_path
    WalkingArrow_cat WalkingArrow_cat
    Terminal_cat Terminal_cat
    (@Terminal_prof WalkingArrow_cat Terminal_cat)
    (@Prof_reindex
      (@DirectedSimplex_cat (succ (succ zero)))
      WalkingArrow_cat
      (@DirectedSimplex_cat (succ (succ zero)))
      Terminal_cat
      (@Unit_prof (@DirectedSimplex_cat (succ (succ zero))))
      (@join_fst_func WalkingArrow_cat Terminal_cat)
      (@join_snd_func WalkingArrow_cat Terminal_cat))
    (@join_cross_transf WalkingArrow_cat Terminal_cat)
    (@id_func WalkingArrow_cat)
    profiled_terminal
    walking_arrow_tgt Terminal_obj;

// Compose the reindex component with the generic join-map generator beta.
symbol profiled_cross02_selected_func_path
  : τ (@=
      (Obj (Functor_cat
        Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base02)))
      profiled_cross02_func
      (@join_map_target_generator_func
        WalkingArrow_cat Terminal_cat
        profiled_vertex0 profiled_terminal))
≔ @eq_trans
    (Obj (Functor_cat
      Terminal_cat
      (Fibre_cat profiled_source_prof profiled_base02)))
    profiled_cross02_func
    (@join_map_source_generator_func
      WalkingArrow_cat Terminal_cat
      profiled_vertex0 profiled_terminal)
    (@join_map_target_generator_func
      WalkingArrow_cat Terminal_cat
      profiled_vertex0 profiled_terminal)
    profiled_cross02_reindex_path
    (@join_map_generator_beta
      WalkingArrow_cat Terminal_cat
      profiled_vertex0 profiled_terminal);

symbol profiled_cross12_selected_func_path
  : τ (@=
      (Obj (Functor_cat
        Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base12)))
      profiled_cross12_func
      (@join_map_target_generator_func
        WalkingArrow_cat Terminal_cat
        profiled_vertex1 profiled_terminal))
≔ @eq_trans
    (Obj (Functor_cat
      Terminal_cat
      (Fibre_cat profiled_source_prof profiled_base12)))
    profiled_cross12_func
    (@join_map_source_generator_func
      WalkingArrow_cat Terminal_cat
      profiled_vertex1 profiled_terminal)
    (@join_map_target_generator_func
      WalkingArrow_cat Terminal_cat
      profiled_vertex1 profiled_terminal)
    profiled_cross12_reindex_path
    (@join_map_generator_beta
      WalkingArrow_cat Terminal_cat
      profiled_vertex1 profiled_terminal);

symbol profiled_cross02_point
  : τ (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
≔ @fapp0
    Terminal_cat
    (Fibre_cat profiled_source_prof profiled_base02)
    profiled_cross02_func
    Terminal_obj;

symbol profiled_cross12_point
  : τ (Obj (Fibre_cat
      profiled_source_prof profiled_base12))
≔ @fapp0
    Terminal_cat
    (Fibre_cat profiled_source_prof profiled_base12)
    profiled_cross12_func
    Terminal_obj;

// Point projections are the selected 02 and 12 ordinary edge generators.
symbol profiled_cross02_selected_path
  : τ (@=
      (Obj (Fibre_cat
        profiled_source_prof profiled_base02))
      profiled_cross02_point
      (@ordinal_simplex1_arrow
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_two_func))
≔ @eq_ap
    (Obj (Functor_cat
      Terminal_cat
      (Fibre_cat profiled_source_prof profiled_base02)))
    (Obj (Fibre_cat profiled_source_prof profiled_base02))
    (λ K : τ (Functor Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base02)),
      @fapp0
        Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base02)
        K Terminal_obj)
    profiled_cross02_func
    (@join_map_target_generator_func
      WalkingArrow_cat Terminal_cat
      profiled_vertex0 profiled_terminal)
    profiled_cross02_selected_func_path;

symbol profiled_cross12_selected_path
  : τ (@=
      (Obj (Fibre_cat
        profiled_source_prof profiled_base12))
      profiled_cross12_point
      (@ordinal_simplex1_arrow
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_one_two_func))
≔ @eq_ap
    (Obj (Functor_cat
      Terminal_cat
      (Fibre_cat profiled_source_prof profiled_base12)))
    (Obj (Fibre_cat profiled_source_prof profiled_base12))
    (λ K : τ (Functor Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base12)),
      @fapp0
        Terminal_cat
        (Fibre_cat profiled_source_prof profiled_base12)
        K Terminal_obj)
    profiled_cross12_func
    (@join_map_target_generator_func
      WalkingArrow_cat Terminal_cat
      profiled_vertex1 profiled_terminal)
    profiled_cross12_selected_func_path;

// The opposite walking generator supplies the naturality direction 12 -> 02.
symbol profiled_source_base_arrow
  : τ (Hom
      (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat)
      profiled_base12 profiled_base02)
≔ @Product_pair
    (Hom_cat (Op_cat WalkingArrow_cat)
      walking_arrow_tgt walking_arrow_src)
    (Hom_cat Terminal_cat Terminal_obj Terminal_obj)
    walking_arrow_generator Terminal_obj;

symbol profiled_source_raw_lhs
  : τ (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
≔ @fapp0
    (Fibre_cat
      (@Terminal_prof WalkingArrow_cat Terminal_cat)
      profiled_base12)
    (Fibre_cat profiled_source_prof profiled_base02)
    (@functord_transport_lhs_func
      (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat)
      (@Terminal_prof WalkingArrow_cat Terminal_cat)
      profiled_source_prof
      profiled_source_cross
      profiled_base12 profiled_base02
      profiled_source_base_arrow)
    Terminal_obj;

symbol profiled_source_raw_rhs
  : τ (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
≔ @fapp0
    (Fibre_cat
      (@Terminal_prof WalkingArrow_cat Terminal_cat)
      profiled_base12)
    (Fibre_cat profiled_source_prof profiled_base02)
    (@functord_transport_rhs_func
      (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat)
      (@Terminal_prof WalkingArrow_cat Terminal_cat)
      profiled_source_prof
      profiled_source_cross
      profiled_base12 profiled_base02
      profiled_source_base_arrow)
    Terminal_obj;


symbol profiled_source_expected_lhs
  : τ (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
≔ @comp_fapp0
    (@DirectedSimplex_cat (succ (succ zero)))
    (@ordinal_simplex1_source
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@ordinal_simplex1_target
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@ordinal_simplex1_target
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_two_func)
    profiled_cross12_point
    (@ordinal_simplex1_arrow
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func);

// The retained terminal-coordinate action is propositionally identity.
symbol profiled_source_terminal_action
  : τ (Hom
      (@DirectedSimplex_cat (succ (succ zero)))
      (@fapp0 Terminal_cat
        (@DirectedSimplex_cat (succ (succ zero)))
        (@join_map_right_func
          WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
          profiled_terminal)
        Terminal_obj)
      (@fapp0 Terminal_cat
        (@DirectedSimplex_cat (succ (succ zero)))
        (@join_map_right_func
          WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
          profiled_terminal)
        Terminal_obj))
≔ @fapp1_fapp0
    Terminal_cat
    (@DirectedSimplex_cat (succ (succ zero)))
    (@join_map_right_func
      WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
      profiled_terminal)
    Terminal_obj Terminal_obj Terminal_obj;

symbol profiled_source_terminal_action_path
  : τ (@=
      (Hom
        (@DirectedSimplex_cat (succ (succ zero)))
        (@fapp0 Terminal_cat
          (@DirectedSimplex_cat (succ (succ zero)))
          (@join_map_right_func
            WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
            profiled_terminal)
          Terminal_obj)
        (@fapp0 Terminal_cat
          (@DirectedSimplex_cat (succ (succ zero)))
          (@join_map_right_func
            WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
            profiled_terminal)
          Terminal_obj))
      profiled_source_terminal_action
      (@id
        (@DirectedSimplex_cat (succ (succ zero)))
        (@fapp0 Terminal_cat
          (@DirectedSimplex_cat (succ (succ zero)))
          (@join_map_right_func
            WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
            profiled_terminal)
          Terminal_obj)))
≔ @fapp1_id_path
    Terminal_cat
    (@DirectedSimplex_cat (succ (succ zero)))
    (@join_map_right_func
      WalkingArrow_cat Terminal_cat WalkingArrow_cat Terminal_cat
      profiled_terminal)
    Terminal_obj;

symbol profiled_source_lhs_identity_mid
  : τ (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
≔ @Hom_fapp0
    (@DirectedSimplex_cat (succ (succ zero)))
    (@ordinal_simplex1_target
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@ordinal_simplex1_source
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@ordinal_simplex1_target
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_two_func)
    (@ordinal_simplex1_target
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_two_func)
    (@ordinal_simplex1_arrow
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@id
      (@DirectedSimplex_cat (succ (succ zero)))
      (@ordinal_simplex1_target
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_two_func))
    profiled_cross12_point;

symbol profiled_source_lhs_identity_path
  : τ (@=
      (Obj (Fibre_cat
        profiled_source_prof profiled_base02))
      profiled_source_raw_lhs
      profiled_source_lhs_identity_mid)
≔ @eq_ap
    (Hom
      (@DirectedSimplex_cat (succ (succ zero)))
      (@ordinal_simplex1_target
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_two_func)
      (@ordinal_simplex1_target
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_two_func))
    (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
    (λ f : τ (Hom
        (@DirectedSimplex_cat (succ (succ zero)))
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_two_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_two_func)),
      @Hom_fapp0
        (@DirectedSimplex_cat (succ (succ zero)))
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_source
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_two_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_two_func)
        (@ordinal_simplex1_arrow
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        f profiled_cross12_point)
    profiled_source_terminal_action
    (@id
      (@DirectedSimplex_cat (succ (succ zero)))
      (@ordinal_simplex1_target
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_two_func))
    profiled_source_terminal_action_path;

symbol profiled_source_lhs_expected_mid_path
  : τ (@=
      (Obj (Fibre_cat
        profiled_source_prof profiled_base02))
      profiled_source_lhs_identity_mid
      profiled_source_expected_lhs)
≔ @eq_refl
    (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
    profiled_source_lhs_identity_mid;

symbol profiled_source_lhs_expected_path
  : τ (@=
      (Obj (Fibre_cat
        profiled_source_prof profiled_base02))
      profiled_source_raw_lhs
      profiled_source_expected_lhs)
≔ @eq_trans
    (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
    profiled_source_raw_lhs
    profiled_source_lhs_identity_mid
    profiled_source_expected_lhs
    profiled_source_lhs_identity_path
    profiled_source_lhs_expected_mid_path;

symbol profiled_source_raw_cell
  : τ (Hom
      (Fibre_cat profiled_source_prof profiled_base02)
      profiled_source_raw_lhs
      profiled_source_raw_rhs)
≔ @fdapp1_int_cell
    (Product_cat (Op_cat WalkingArrow_cat) Terminal_cat)
    (@Terminal_prof WalkingArrow_cat Terminal_cat)
    profiled_source_prof
    profiled_source_cross
    profiled_base12 profiled_base02
    profiled_source_base_arrow
    Terminal_obj;

// First conjugate only the formal left endpoint to readable composition.
symbol profiled_source_readable_cell
  : τ (Hom
      (Fibre_cat profiled_source_prof profiled_base02)
      profiled_source_expected_lhs
      profiled_cross02_point)
≔ @comp_fapp0
    (Fibre_cat profiled_source_prof profiled_base02)
    profiled_source_expected_lhs
    profiled_source_raw_lhs
    profiled_cross02_point
    profiled_source_raw_cell
    (@path_to_hom
      (Fibre_cat profiled_source_prof profiled_base02)
      profiled_source_expected_lhs
      profiled_source_raw_lhs
      (@eq_sym
        (Obj (Fibre_cat
          profiled_source_prof profiled_base02))
        profiled_source_raw_lhs
        profiled_source_expected_lhs
        profiled_source_lhs_expected_path));

// Mapping the 12 endpoint path through postcomposition aligns the source.
symbol profiled_source_expected_selected_lhs
  : τ (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
≔ @comp_fapp0
    (@DirectedSimplex_cat (succ (succ zero)))
    (@ordinal_simplex1_source
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@ordinal_simplex1_target
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@ordinal_simplex1_target
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_two_func)
    (@ordinal_simplex1_arrow
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_one_two_func)
    (@ordinal_simplex1_arrow
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func);

symbol profiled_source_selected_lhs_path
  : τ (@=
      (Obj (Fibre_cat
        profiled_source_prof profiled_base02))
      profiled_source_expected_lhs
      profiled_source_expected_selected_lhs)
≔ @eq_ap
    (Obj (Fibre_cat
      profiled_source_prof profiled_base12))
    (Obj (Fibre_cat
      profiled_source_prof profiled_base02))
    (λ h : τ (Obj (Fibre_cat
        profiled_source_prof profiled_base12)),
      @comp_fapp0
        (@DirectedSimplex_cat (succ (succ zero)))
        (@ordinal_simplex1_source
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_two_func)
        h
        (@ordinal_simplex1_arrow
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func))
    profiled_cross12_point
    (@ordinal_simplex1_arrow
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_one_two_func)
    profiled_cross12_selected_path;

// Conjugate both readable endpoints to the selected ordinal edges.
symbol profiled_source_selected_cell
  : τ (Hom
      (Fibre_cat profiled_source_prof profiled_base02)
      profiled_source_expected_selected_lhs
      (@ordinal_simplex1_arrow
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_two_func))
≔ @comp_fapp0
    (Fibre_cat profiled_source_prof profiled_base02)
    profiled_source_expected_selected_lhs
    profiled_source_expected_lhs
    (@ordinal_simplex1_arrow
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_two_func)
    (@comp_fapp0
      (Fibre_cat profiled_source_prof profiled_base02)
      profiled_source_expected_lhs
      profiled_cross02_point
      (@ordinal_simplex1_arrow
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_two_func)
      (@path_to_hom
        (Fibre_cat profiled_source_prof profiled_base02)
        profiled_cross02_point
        (@ordinal_simplex1_arrow
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_two_func)
        profiled_cross02_selected_path)
      profiled_source_readable_cell)
    (@path_to_hom
      (Fibre_cat profiled_source_prof profiled_base02)
      profiled_source_expected_selected_lhs
      profiled_source_expected_lhs
      (@eq_sym
        (Obj (Fibre_cat
          profiled_source_prof profiled_base02))
        profiled_source_expected_lhs
        profiled_source_expected_selected_lhs
        profiled_source_selected_lhs_path));

// The selected conjugated cell is the canonical native source filler for the
// identity ordinal triangle.
symbol ordinal_simplex2_source_canonical_filler
  : τ (@OrdinalDependentSimplex2CanonicalFiller
      (@DirectedSimplex_cat (succ (succ zero)))
      (@id_func (@DirectedSimplex_cat (succ (succ zero)))))
≔ profiled_source_selected_cell;

// Package the source filler through the existing ordinal/native constructor.
symbol ordinal_simplex2_source_observation
  : τ (@DependentSimplexObservation
      (@DirectedSimplex_cat (succ (succ zero)))
      (succ (succ zero)))
≔ @ordinal_dependent_simplex2_observe
    (@DirectedSimplex_cat (succ (succ zero)))
    (@id_func (@DirectedSimplex_cat (succ (succ zero))))
    ordinal_simplex2_source_canonical_filler;

symbol ordinal_simplex2_source_native
  : τ (Obj (@DependentSimplex2_cat
      (@DirectedSimplex_cat (succ (succ zero)))
      (@ordinal_simplex1_source
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_one_func)
      (@dependent_simplex1
        (@DirectedSimplex_cat (succ (succ zero)))
        (@ordinal_simplex1_source
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_arrow
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func))))
≔ sigma_Snd ordinal_simplex2_source_observation;

// Map that native source simplex under an arbitrary ordinal triangle H.
symbol ordinal_dependent_simplex2_mapped_native
  [C : Cat]
  (H : τ (Functor
    (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (Obj (@DependentSimplex2_cat
      C
      (@fapp0
        (@DirectedSimplex_cat (succ (succ zero))) C H
        (@ordinal_simplex1_source
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func))
      (@fapp0
        (@DependentSimplex1_cat
          (@DirectedSimplex_cat (succ (succ zero)))
          (@ordinal_simplex1_source
            (@DirectedSimplex_cat (succ (succ zero)))
            simplex_edge_zero_one_func))
        (@DependentSimplex1_cat C
          (@fapp0
            (@DirectedSimplex_cat (succ (succ zero))) C H
            (@ordinal_simplex1_source
              (@DirectedSimplex_cat (succ (succ zero)))
              simplex_edge_zero_one_func)))
        (@dependent_simplex1_map
          (@DirectedSimplex_cat (succ (succ zero))) C H
          (@ordinal_simplex1_source
            (@DirectedSimplex_cat (succ (succ zero)))
            simplex_edge_zero_one_func))
        (@dependent_simplex1
          (@DirectedSimplex_cat (succ (succ zero)))
          (@ordinal_simplex1_source
            (@DirectedSimplex_cat (succ (succ zero)))
            simplex_edge_zero_one_func)
          (@ordinal_simplex1_target
            (@DirectedSimplex_cat (succ (succ zero)))
            simplex_edge_zero_one_func)
          (@ordinal_simplex1_arrow
            (@DirectedSimplex_cat (succ (succ zero)))
            simplex_edge_zero_one_func)))))
≔ @fapp0
    (@DependentSimplex2_cat
      (@DirectedSimplex_cat (succ (succ zero)))
      (@ordinal_simplex1_source
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_one_func)
      (@dependent_simplex1
        (@DirectedSimplex_cat (succ (succ zero)))
        (@ordinal_simplex1_source
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_arrow
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)))
    _
    (@dependent_simplex2_map
      (@DirectedSimplex_cat (succ (succ zero))) C H
      (@ordinal_simplex1_source
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_one_func)
      (@dependent_simplex1
        (@DirectedSimplex_cat (succ (succ zero)))
        (@ordinal_simplex1_source
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_target
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)
        (@ordinal_simplex1_arrow
          (@DirectedSimplex_cat (succ (succ zero)))
          simplex_edge_zero_one_func)))
    ordinal_simplex2_source_native;

// The top component of the mapped native simplex is the arbitrary-H canonical
// ordinal filler.
symbol ordinal_dependent_simplex2_canonical_filler
  [C : Cat]
  (H : τ (Functor
    (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (@OrdinalDependentSimplex2CanonicalFiller C H)
≔ sigma_Snd (sigma_Snd
    (@ordinal_dependent_simplex2_mapped_native C H));

// Public unconditional dimension-two ordinal/dependent observation.
symbol ordinal_dependent_simplex2_observe_canonical
  [C : Cat]
  (H : τ (Functor (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (@DependentSimplexObservation C (succ (succ zero)))
≔ @ordinal_dependent_simplex2_observe
    C H (@ordinal_dependent_simplex2_canonical_filler C H);

// Whole native dimension-two map retained behind the filler projection.
symbol ordinal_dependent_simplex2_native_map
  [C : Cat]
  (H : τ (Functor
    (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (Functor _ _)
≔ @dependent_simplex2_map
    (@DirectedSimplex_cat (succ (succ zero))) C H
    (@ordinal_simplex1_source
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_one_func)
    (@dependent_simplex1
      (@DirectedSimplex_cat (succ (succ zero)))
      (@ordinal_simplex1_source
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_one_func)
      (@ordinal_simplex1_target
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_one_func)
      (@ordinal_simplex1_arrow
        (@DirectedSimplex_cat (succ (succ zero)))
        simplex_edge_zero_one_func));

// One further hom action remains available for the dimension-three handoff.
symbol ordinal_dependent_simplex2_next_func
  [C : Cat]
  (H : τ (Functor
    (@DirectedSimplex_cat (succ (succ zero))) C))
  : τ (Functor
      (Hom_cat _
        ordinal_simplex2_source_native
        ordinal_simplex2_source_native)
      (Hom_cat _
        (@ordinal_dependent_simplex2_mapped_native C H)
        (@ordinal_dependent_simplex2_mapped_native C H)))
≔ @fapp1_func
    _ _ (@ordinal_dependent_simplex2_native_map C H)
    ordinal_simplex2_source_native
    ordinal_simplex2_source_native;
