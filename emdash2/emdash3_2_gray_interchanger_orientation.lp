/*
  Emdash v3.2: typed readable orientation of the selected Gray interchanger.

  The active interchanger remains owned by the whole post/left internal
  action.  This module derives first-class paths from its stable displayed
  endpoints to the two visible composites around the walking square.  The
  result confirms the direction

      inner_target[g] o outer_source
        ==> outer_target o inner_source[g].

  In the native cubical notation this is `v o a ==> b o u`, opposite to the
  selected `LaxArrow_cat` filler `b o u ==> v o a`.  The verdict is therefore
  an orientation boundary for the later Gray-cube decoder, not permission to
  invert a directed cell or identify its endpoints.

  The derivation uses the generic internal-action beta, whole displayed
  strict-naturality paths, stable postcomposition reading, and the existing
  pre/right PathOut reframe.  It adds no rule, unifier, endpoint collapse, or
  independent interchanger.
*/

require open emdash.emdash3_2_gray_interchanger;
require open emdash.emdash3_2_pathout_transformation_reframing;
require open emdash.emdash3_2_cubical_arrow;

// Stable represented reading of G[g] o epsilon_X.
protected symbol gray_interchanger_post_stable
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @hom_postcomp_fapp0
    GrayWalkingSquare_cat
    WalkingArrow_cat
    gray_square_inner_tgt_func
    gray_square_obj00
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator
    gray_square_outer_src_arrow;

// Stable represented reading of epsilon_Z o F[g].
protected symbol gray_interchanger_pre_stable
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @pathout_sigma_source
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    gray_square_outer_transf
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator;

// The stable postcomposition owner has the visible v o a reading.
protected symbol gray_interchanger_post_raw_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_post_stable
      gray_square_post_composite)
≔ @path_pseudo_laxity_postcomp_comp_path
    GrayWalkingSquare_cat
    WalkingArrow_cat
    gray_square_inner_tgt_func
    gray_square_obj00
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator
    gray_square_outer_src_arrow;

// The stable precomposition owner has the visible b o u reading.
protected symbol gray_interchanger_pre_raw_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_pre_stable
      gray_square_pre_composite)
≔ @pathout_sigma_raw_path
    WalkingArrow_cat
    GrayWalkingSquare_cat
    gray_square_inner_src_func
    gray_square_inner_tgt_func
    gray_square_outer_transf
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator;

// Common fixed-generator internal action selected by both whole strict paths.
protected symbol gray_interchanger_common_func
  : τ (Functor GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)
≔ @functord_transport_func
    WalkingArrow_cat
    (@hom_
      WalkingArrow_cat
      WalkingArrow_cat
      (@id_func WalkingArrow_cat)
      walking_arrow_src)
    (@hom_
      GrayWalkingSquare_cat
      WalkingArrow_cat
      gray_square_inner_tgt_func
      gray_square_obj00)
    (@tapp1_at_transf
      WalkingArrow_cat
      GrayWalkingSquare_cat
      gray_square_inner_src_func
      gray_square_inner_tgt_func
      walking_arrow_src
      gray_square_outer_transf)
    walking_arrow_src
    walking_arrow_tgt
    walking_arrow_generator;

protected symbol gray_interchanger_common_value
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @fapp0
    GrayInterchangerDomain_cat
    GrayInterchangerCodomain_cat
    gray_interchanger_common_func
    gray_interchanger_base_identity;

// The two formal endpoints meet at the common internal action by the existing
// whole displayed strict-naturality paths.
protected symbol gray_interchanger_source_common_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_source
      gray_interchanger_common_value)
≔ @eq_ap
    (Obj (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat))
    (Obj GrayInterchangerCodomain_cat)
    (λ H : τ (Obj (Functor_cat
        GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)),
      @fapp0
        GrayInterchangerDomain_cat GrayInterchangerCodomain_cat
        H gray_interchanger_base_identity)
    gray_interchanger_lhs_func
    gray_interchanger_common_func
    (@functord_transport_lhs_agrees
      WalkingArrow_cat
      (@hom_
        WalkingArrow_cat WalkingArrow_cat
        (@id_func WalkingArrow_cat) walking_arrow_src)
      (@hom_
        GrayWalkingSquare_cat WalkingArrow_cat
        gray_square_inner_tgt_func gray_square_obj00)
      (@tapp1_at_transf
        WalkingArrow_cat GrayWalkingSquare_cat
        gray_square_inner_src_func gray_square_inner_tgt_func
        walking_arrow_src gray_square_outer_transf)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator);

protected symbol gray_interchanger_target_common_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_target
      gray_interchanger_common_value)
≔ @eq_ap
    (Obj (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat))
    (Obj GrayInterchangerCodomain_cat)
    (λ H : τ (Obj (Functor_cat
        GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)),
      @fapp0
        GrayInterchangerDomain_cat GrayInterchangerCodomain_cat
        H gray_interchanger_base_identity)
    gray_interchanger_rhs_func
    gray_interchanger_common_func
    (@functord_transport_rhs_agrees
      WalkingArrow_cat
      (@hom_
        WalkingArrow_cat WalkingArrow_cat
        (@id_func WalkingArrow_cat) walking_arrow_src)
      (@hom_
        GrayWalkingSquare_cat WalkingArrow_cat
        gray_square_inner_tgt_func gray_square_obj00)
      (@tapp1_at_transf
        WalkingArrow_cat GrayWalkingSquare_cat
        gray_square_inner_src_func gray_square_inner_tgt_func
        walking_arrow_src gray_square_outer_transf)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator);

// Keep the post/left base arrow internal for one more projection so the stable
// postcomposition owner remains visible before comparison with the common
// action.
protected symbol gray_interchanger_lhs_tele_func
  : τ (Functor
      (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
      (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat))
≔ @functord_transport_lhs_tele_func
    WalkingArrow_cat
    (@hom_
      WalkingArrow_cat WalkingArrow_cat
      (@id_func WalkingArrow_cat) walking_arrow_src)
    (@hom_
      GrayWalkingSquare_cat WalkingArrow_cat
      gray_square_inner_tgt_func gray_square_obj00)
    (@tapp1_at_transf
      WalkingArrow_cat GrayWalkingSquare_cat
      gray_square_inner_src_func gray_square_inner_tgt_func
      walking_arrow_src gray_square_outer_transf)
    walking_arrow_src walking_arrow_tgt;

protected symbol gray_interchanger_lhs_tele_at_generator
  : τ (Functor GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)
≔ @fapp0
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)
    gray_interchanger_lhs_tele_func walking_arrow_generator;

protected symbol gray_interchanger_lhs_tele_value
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @fapp0
    GrayInterchangerDomain_cat GrayInterchangerCodomain_cat
    gray_interchanger_lhs_tele_at_generator
    gray_interchanger_base_identity;

protected symbol gray_interchanger_lhs_tele_common_func_path
  : τ (@=
      (Obj (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat))
      gray_interchanger_lhs_tele_at_generator
      gray_interchanger_common_func)
≔ @eq_ap
    (Obj (Functor_cat
      (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
      (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)))
    (Obj (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat))
    (λ H : τ (Obj (Functor_cat
        (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
        (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat))),
      @fapp0
        (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
        (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)
        H walking_arrow_generator)
    gray_interchanger_lhs_tele_func
    (@tapp1_func
      WalkingArrow_cat Cat_cat
      (@hom_
        WalkingArrow_cat WalkingArrow_cat
        (@id_func WalkingArrow_cat) walking_arrow_src)
      (@hom_
        GrayWalkingSquare_cat WalkingArrow_cat
        gray_square_inner_tgt_func gray_square_obj00)
      walking_arrow_src walking_arrow_tgt
      (@tapp1_at_transf
        WalkingArrow_cat GrayWalkingSquare_cat
        gray_square_inner_src_func gray_square_inner_tgt_func
        walking_arrow_src gray_square_outer_transf))
    (@functord_transport_lhs_tele_agrees
      WalkingArrow_cat
      (@hom_
        WalkingArrow_cat WalkingArrow_cat
        (@id_func WalkingArrow_cat) walking_arrow_src)
      (@hom_
        GrayWalkingSquare_cat WalkingArrow_cat
        gray_square_inner_tgt_func gray_square_obj00)
      (@tapp1_at_transf
        WalkingArrow_cat GrayWalkingSquare_cat
        gray_square_inner_src_func gray_square_inner_tgt_func
        walking_arrow_src gray_square_outer_transf)
      walking_arrow_src walking_arrow_tgt);

protected symbol gray_interchanger_lhs_tele_common_value_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_lhs_tele_value
      gray_interchanger_common_value)
≔ @eq_ap
    (Obj (Functor_cat GrayInterchangerDomain_cat GrayInterchangerCodomain_cat))
    (Obj GrayInterchangerCodomain_cat)
    (λ H : τ (Obj (Functor_cat
        GrayInterchangerDomain_cat GrayInterchangerCodomain_cat)),
      @fapp0
        GrayInterchangerDomain_cat GrayInterchangerCodomain_cat
        H gray_interchanger_base_identity)
    gray_interchanger_lhs_tele_at_generator
    gray_interchanger_common_func
    gray_interchanger_lhs_tele_common_func_path;

// Pointwise reading of the retained Cat-composition in the left telescope.
protected symbol gray_interchanger_post_composite_value
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @fapp0
    (Hom_cat
      GrayWalkingSquare_cat gray_square_obj00 gray_square_obj10)
    GrayInterchangerCodomain_cat
    (@hom_postcomp_func
      GrayWalkingSquare_cat WalkingArrow_cat
      gray_square_inner_tgt_func gray_square_obj00
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@fapp0
      GrayInterchangerDomain_cat
      (Hom_cat
        GrayWalkingSquare_cat gray_square_obj00 gray_square_obj10)
      (@tapp1_func
        WalkingArrow_cat GrayWalkingSquare_cat
        gray_square_inner_src_func gray_square_inner_tgt_func
        walking_arrow_src walking_arrow_src gray_square_outer_transf)
      gray_interchanger_base_identity);

protected symbol gray_interchanger_lhs_tele_post_composite_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_lhs_tele_value
      gray_interchanger_post_composite_value)
≔ @cat_precomp_composite_component_path
    GrayInterchangerDomain_cat
    (Hom_cat
      GrayWalkingSquare_cat gray_square_obj00 gray_square_obj10)
    GrayInterchangerCodomain_cat
    (@tapp1_func
      WalkingArrow_cat GrayWalkingSquare_cat
      gray_square_inner_src_func gray_square_inner_tgt_func
      walking_arrow_src walking_arrow_src gray_square_outer_transf)
    (@hom_postcomp_func
      GrayWalkingSquare_cat WalkingArrow_cat
      gray_square_inner_tgt_func gray_square_obj00
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    gray_interchanger_base_identity;

protected symbol gray_interchanger_post_composite_reading_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_post_stable
      gray_interchanger_post_composite_value)
≔ @eq_refl
    (Obj GrayInterchangerCodomain_cat)
    gray_interchanger_post_stable;

protected symbol gray_interchanger_post_lhs_tele_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_post_stable
      gray_interchanger_lhs_tele_value)
≔ @eq_trans
    (Obj GrayInterchangerCodomain_cat)
    gray_interchanger_post_stable
    gray_interchanger_post_composite_value
    gray_interchanger_lhs_tele_value
    gray_interchanger_post_composite_reading_path
    (@eq_sym
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_lhs_tele_value
      gray_interchanger_post_composite_value
      gray_interchanger_lhs_tele_post_composite_path);

protected symbol gray_interchanger_post_common_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_post_stable
      gray_interchanger_common_value)
≔ @eq_trans
    (Obj GrayInterchangerCodomain_cat)
    gray_interchanger_post_stable
    gray_interchanger_lhs_tele_value
    gray_interchanger_common_value
    gray_interchanger_post_lhs_tele_path
    gray_interchanger_lhs_tele_common_value_path;

// The existing pre/right reframe reads epsilon[g] as epsilon_Z o F[g].
protected symbol gray_interchanger_pre_formal_value
  : τ (Obj GrayInterchangerCodomain_cat)
≔ @fapp0
    (Hom_cat WalkingArrow_cat walking_arrow_tgt walking_arrow_tgt)
    GrayInterchangerCodomain_cat
    (@pathout_top_lhs_func
      WalkingArrow_cat GrayWalkingSquare_cat
      gray_square_inner_src_func gray_square_inner_tgt_func
      gray_square_outer_transf
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@id WalkingArrow_cat walking_arrow_tgt);

protected symbol gray_interchanger_pre_formal_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_pre_stable
      gray_interchanger_pre_formal_value)
≔ @pathout_sigma_top_source_path
    WalkingArrow_cat GrayWalkingSquare_cat
    gray_square_inner_src_func gray_square_inner_tgt_func
    gray_square_outer_transf
    walking_arrow_src walking_arrow_tgt walking_arrow_generator;

protected symbol gray_interchanger_pre_formal_common_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_pre_formal_value
      gray_interchanger_common_value)
≔ @eq_refl
    (Obj GrayInterchangerCodomain_cat)
    gray_interchanger_common_value;

protected symbol gray_interchanger_pre_common_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_pre_stable
      gray_interchanger_common_value)
≔ @eq_trans
    (Obj GrayInterchangerCodomain_cat)
    gray_interchanger_pre_stable
    gray_interchanger_pre_formal_value
    gray_interchanger_common_value
    gray_interchanger_pre_formal_path
    gray_interchanger_pre_formal_common_path;

// Public typed endpoint readings of the selected whole interchanger.
symbol gray_interchanger_source_readable_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_source
      gray_square_post_composite)
≔ @eq_trans
    (Obj GrayInterchangerCodomain_cat)
    gray_interchanger_source
    gray_interchanger_common_value
    gray_square_post_composite
    gray_interchanger_source_common_path
    (@eq_trans
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_common_value
      gray_interchanger_post_stable
      gray_square_post_composite
      (@eq_sym
        (Obj GrayInterchangerCodomain_cat)
        gray_interchanger_post_stable
        gray_interchanger_common_value
        gray_interchanger_post_common_path)
      gray_interchanger_post_raw_path);

symbol gray_interchanger_target_readable_path
  : τ (@=
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_target
      gray_square_pre_composite)
≔ @eq_trans
    (Obj GrayInterchangerCodomain_cat)
    gray_interchanger_target
    gray_interchanger_common_value
    gray_square_pre_composite
    gray_interchanger_target_common_path
    (@eq_trans
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_common_value
      gray_interchanger_pre_stable
      gray_square_pre_composite
      (@eq_sym
        (Obj GrayInterchangerCodomain_cat)
        gray_interchanger_pre_stable
        gray_interchanger_common_value
        gray_interchanger_pre_common_path)
      gray_interchanger_pre_raw_path);

// Capped readable reframe of the same directed cell.  The source equality is
// reversed only to precompose the formal cell; the cell itself is not inverted.
protected symbol gray_interchanger_source_reframe
  : τ (Hom
      GrayInterchangerCodomain_cat
      gray_square_post_composite
      gray_interchanger_source)
≔ @path_to_hom
    GrayInterchangerCodomain_cat
    gray_square_post_composite
    gray_interchanger_source
    (@eq_sym
      (Obj GrayInterchangerCodomain_cat)
      gray_interchanger_source
      gray_square_post_composite
      gray_interchanger_source_readable_path);

protected symbol gray_interchanger_target_reframe
  : τ (Hom
      GrayInterchangerCodomain_cat
      gray_interchanger_target
      gray_square_pre_composite)
≔ @path_to_hom
    GrayInterchangerCodomain_cat
    gray_interchanger_target
    gray_square_pre_composite
    gray_interchanger_target_readable_path;

symbol gray_interchanger_readable
  : τ (Hom
      GrayInterchangerCodomain_cat
      gray_square_post_composite
      gray_square_pre_composite)
≔ @comp_fapp0
    GrayInterchangerCodomain_cat
    gray_square_post_composite
    gray_interchanger_target
    gray_square_pre_composite
    gray_interchanger_target_reframe
    (@comp_fapp0
      GrayInterchangerCodomain_cat
      gray_square_post_composite
      gray_interchanger_source
      gray_interchanger_target
      gray_interchanger
      gray_interchanger_source_reframe);

/*
  Coordinate-swapped native square.  The outer-coordinate arrows are now the
  source and target edge objects, while the inner-coordinate arrows are the
  two sides.  Its native boundary is therefore

      inner_target o outer_source
        ==> outer_target o inner_source,

  exactly the checked direction of `gray_interchanger_readable`.
*/
symbol gray_interchanger_swapped_square
  : τ (Hom
      (@CubicalArrow_cat GrayWalkingSquare_cat)
      (@cubical_edge
        GrayWalkingSquare_cat
        gray_square_obj00 gray_square_obj10
        gray_square_outer_src_arrow)
      (@cubical_edge
        GrayWalkingSquare_cat
        gray_square_obj01 gray_square_obj11
        gray_square_outer_tgt_arrow))
≔ @cubical_square
    GrayWalkingSquare_cat
    gray_square_obj00 gray_square_obj01
    gray_square_obj10 gray_square_obj11
    gray_square_outer_src_arrow
    gray_square_outer_tgt_arrow
    gray_square_inner_src_arrow
    gray_square_inner_tgt_arrow
    gray_interchanger_readable;
