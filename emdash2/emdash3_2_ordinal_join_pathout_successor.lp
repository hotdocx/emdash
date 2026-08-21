/*
  Generic shaped outgoing-path comparison for the ordinal successor A * 1.

  Identity action on the old branch and the selected strict terminal profile
  determine one join extension.  Its observed and primitive cross cells are
  propositionally equal; fixing any old object turns that whole comparison
  into a transformation between outgoing-path maps.  The result is generic in
  A and can be iterated by pathout_transf_lift.  No dimension-specific simplex
  data, endpoint rule, or proof-time unifier is introduced.
*/

require open emdash.emdash3_2_pathout_transformation_lift;
require open emdash.emdash3_2_join_cross_compatibility;

symbol ordinal_join_terminal_func
  : τ (Functor Terminal_cat Terminal_cat)
≔ @strict_functor_carrier
    Terminal_cat Terminal_cat
    (@strict_identity_data Terminal_cat);

symbol ordinal_join_target_cat
  (A : Cat)
  : Cat
≔ @Join_cat A Terminal_cat;

symbol ordinal_join_left_func
  (A : Cat)
  : τ (Functor A (@ordinal_join_target_cat A))
≔ @join_fst_func A Terminal_cat;

symbol ordinal_join_right_func
  (A : Cat)
  : τ (Functor Terminal_cat (@ordinal_join_target_cat A))
≔ @join_map_right_func
    A Terminal_cat A Terminal_cat ordinal_join_terminal_func;

symbol ordinal_join_cross
  (A : Cat)
  : τ (Obj (@Prof_transf_cat
      (@ordinal_join_target_cat A)
      A
      (@ordinal_join_target_cat A) Terminal_cat
      (@Terminal_prof A Terminal_cat)
      (@ordinal_join_left_func A)
      (@Unit_prof (@ordinal_join_target_cat A))
      (@ordinal_join_right_func A)))
≔ @join_map_cross_transf
    A Terminal_cat A Terminal_cat
    (@id_func A) ordinal_join_terminal_func;

symbol ordinal_join_data
  (A : Cat)
  : τ (@JoinMapObjectData
      A Terminal_cat (@ordinal_join_target_cat A))
≔ @Struct_sigma
    (Functor A (@ordinal_join_target_cat A))
    (λ first : τ (Functor A (@ordinal_join_target_cat A)),
      @Σ_
        (Functor Terminal_cat (@ordinal_join_target_cat A))
        (λ second : τ (Functor
            Terminal_cat (@ordinal_join_target_cat A)),
          Obj (@Prof_transf_cat
            (@ordinal_join_target_cat A)
            A
            (@ordinal_join_target_cat A) Terminal_cat
            (@Terminal_prof A Terminal_cat)
            first
            (@Unit_prof (@ordinal_join_target_cat A))
            second)))
    (@ordinal_join_left_func A)
    (@Struct_sigma
      (Functor Terminal_cat (@ordinal_join_target_cat A))
      (λ second : τ (Functor
          Terminal_cat (@ordinal_join_target_cat A)),
        Obj (@Prof_transf_cat
          (@ordinal_join_target_cat A)
          A
          (@ordinal_join_target_cat A) Terminal_cat
          (@Terminal_prof A Terminal_cat)
          (@ordinal_join_left_func A)
          (@Unit_prof (@ordinal_join_target_cat A))
          second))
      (@ordinal_join_right_func A)
      (@ordinal_join_cross A));

symbol ordinal_join_shape_left
  (A : Cat)
  : τ (Functor A A)
≔ @id_func A;

symbol ordinal_join_shape_right
  (A : Cat)
  : τ (Functor A Terminal_cat)
≔ @Const_func A Terminal_cat Terminal_obj;

symbol ordinal_join_beta_left
  (A : Cat)
  : τ (Functor A (@ordinal_join_target_cat A))
≔ @comp_cat_fapp0
    A A (@ordinal_join_target_cat A)
    (@join_map_object_left
      A Terminal_cat (@ordinal_join_target_cat A)
      (@ordinal_join_data A))
    (@ordinal_join_shape_left A);

symbol ordinal_join_beta_right
  (A : Cat)
  : τ (Functor A (@ordinal_join_target_cat A))
≔ @comp_cat_fapp0
    A Terminal_cat (@ordinal_join_target_cat A)
    (@join_map_object_right
      A Terminal_cat (@ordinal_join_target_cat A)
      (@ordinal_join_data A))
    (@ordinal_join_shape_right A);

symbol ordinal_join_observed_cone
  (A : Cat)
  : τ (@Prof_hom
      A
      (@ordinal_join_target_cat A)
      (@ordinal_join_target_cat A)
      (@ordinal_join_beta_left A)
      (@Unit_prof (@ordinal_join_target_cat A))
      (@ordinal_join_beta_right A))
≔ @join_map_observe_cross_at
    A Terminal_cat
    (@ordinal_join_target_cat A) A
    (@join_map_extend_object
      A Terminal_cat (@ordinal_join_target_cat A)
      (@ordinal_join_data A))
    (@ordinal_join_shape_left A)
    (@ordinal_join_shape_right A);

symbol ordinal_join_primitive_cone
  (A : Cat)
  : τ (@Prof_hom
      A
      (@ordinal_join_target_cat A)
      (@ordinal_join_target_cat A)
      (@ordinal_join_beta_left A)
      (@Unit_prof (@ordinal_join_target_cat A))
      (@ordinal_join_beta_right A))
≔ @Prof_cell_eval
    A A Terminal_cat
    (@ordinal_join_target_cat A)
    (@ordinal_join_target_cat A)
    (@Unit_prof (@ordinal_join_target_cat A))
    (@join_map_object_left
      A Terminal_cat (@ordinal_join_target_cat A)
      (@ordinal_join_data A))
    (@join_map_object_right
      A Terminal_cat (@ordinal_join_target_cat A)
      (@ordinal_join_data A))
    (@ordinal_join_shape_left A)
    (@ordinal_join_shape_right A)
    (@join_map_extend_cross
      A Terminal_cat (@ordinal_join_target_cat A)
      (@ordinal_join_data A));

symbol ordinal_join_cone_path
  (A : Cat)
  : τ (@=
      (@Prof_hom
        A
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_cat A)
        (@ordinal_join_beta_left A)
        (@Unit_prof (@ordinal_join_target_cat A))
        (@ordinal_join_beta_right A))
      (@ordinal_join_observed_cone A)
      (@ordinal_join_primitive_cone A))
≔ @join_map_extend_cross_shaped_beta
    A Terminal_cat (@ordinal_join_target_cat A) A
    (@ordinal_join_data A)
    (@ordinal_join_shape_left A)
    (@ordinal_join_shape_right A);

symbol ordinal_join_target_base
  (A : Cat)
  (x0 : τ (Obj A))
  : τ (Obj (@ordinal_join_target_cat A))
≔ @fapp0
    A (@ordinal_join_target_cat A)
    (@ordinal_join_beta_left A) x0;

symbol ordinal_join_observed_pathout
  (A : Cat)
  (x0 : τ (Obj A))
  : τ (Functor
      (@PathOut_cat A x0)
      (@PathOut_cat
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_base A x0)))
≔ @shaped_pathout_func
    A (@ordinal_join_target_cat A)
    (@ordinal_join_beta_left A)
    (@ordinal_join_beta_right A)
    (@ordinal_join_observed_cone A) x0;

symbol ordinal_join_primitive_pathout
  (A : Cat)
  (x0 : τ (Obj A))
  : τ (Functor
      (@PathOut_cat A x0)
      (@PathOut_cat
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_base A x0)))
≔ @shaped_pathout_func
    A (@ordinal_join_target_cat A)
    (@ordinal_join_beta_left A)
    (@ordinal_join_beta_right A)
    (@ordinal_join_primitive_cone A) x0;

symbol ordinal_join_pathout_path
  (A : Cat)
  (x0 : τ (Obj A))
  : τ (@=
      (Obj (Functor_cat
        (@PathOut_cat A x0)
        (@PathOut_cat
          (@ordinal_join_target_cat A)
          (@ordinal_join_target_base A x0))))
      (@ordinal_join_observed_pathout A x0)
      (@ordinal_join_primitive_pathout A x0))
≔ @eq_ap
    (@Prof_hom
      A
      (@ordinal_join_target_cat A)
      (@ordinal_join_target_cat A)
      (@ordinal_join_beta_left A)
      (@Unit_prof (@ordinal_join_target_cat A))
      (@ordinal_join_beta_right A))
    (Obj (Functor_cat
      (@PathOut_cat A x0)
      (@PathOut_cat
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_base A x0))))
    (λ cone : τ (@Prof_hom
        A
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_cat A)
        (@ordinal_join_beta_left A)
        (@Unit_prof (@ordinal_join_target_cat A))
        (@ordinal_join_beta_right A)),
      @shaped_pathout_func
        A (@ordinal_join_target_cat A)
        (@ordinal_join_beta_left A)
        (@ordinal_join_beta_right A)
        cone x0)
    (@ordinal_join_observed_cone A)
    (@ordinal_join_primitive_cone A)
    (@ordinal_join_cone_path A);

symbol ordinal_join_pathout_transf
  (A : Cat)
  (x0 : τ (Obj A))
  : τ (Transf
      (@ordinal_join_observed_pathout A x0)
      (@ordinal_join_primitive_pathout A x0))
≔ @path_to_hom
    (Functor_cat
      (@PathOut_cat A x0)
      (@PathOut_cat
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_base A x0)))
    (@ordinal_join_observed_pathout A x0)
    (@ordinal_join_primitive_pathout A x0)
    (@ordinal_join_pathout_path A x0);

// The comparison can immediately be lifted one recursive PathOut level.
type λ A : Cat, λ x0 : τ (Obj A),
  λ e01 : τ (Obj (@PathOut_cat A x0)),
    @pathout_transf_lift
      (@PathOut_cat A x0)
      (@PathOut_cat
        (@ordinal_join_target_cat A)
        (@ordinal_join_target_base A x0))
      (@ordinal_join_observed_pathout A x0)
      (@ordinal_join_primitive_pathout A x0)
      (@ordinal_join_pathout_transf A x0)
      e01;
