/* Reviewer for whole terminal-right profunctor-action normalization. */

require open emdash.emdash3_2_prof_reindex_terminal_normalization;

constant symbol prof_terminal_test_A : Cat;
constant symbol prof_terminal_test_B : Cat;

constant symbol prof_terminal_test_F
  : τ (Functor prof_terminal_test_A prof_terminal_test_B);

constant symbol prof_terminal_test_G
  : τ (Functor Terminal_cat prof_terminal_test_B);

constant symbol prof_terminal_test_W
  : τ (Obj prof_terminal_test_A);

constant symbol prof_terminal_test_X
  : τ (Obj prof_terminal_test_A);

constant symbol prof_terminal_test_g
  : τ (Hom prof_terminal_test_B
      (@fapp0
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_X)
      (@fapp0
        Terminal_cat prof_terminal_test_B
        prof_terminal_test_G Terminal_obj));

constant symbol prof_terminal_test_h
  : τ (Hom prof_terminal_test_B
      (@fapp0
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_W)
      (@fapp0
        Terminal_cat prof_terminal_test_B
        prof_terminal_test_G Terminal_obj));

constant symbol prof_terminal_test_normal
  : τ (@=
      (Hom prof_terminal_test_B
        (@fapp0
          Terminal_cat prof_terminal_test_B
          prof_terminal_test_G Terminal_obj)
        (@fapp0
          Terminal_cat prof_terminal_test_B
          prof_terminal_test_G Terminal_obj))
      (@prof_terminal_terminal_action
        prof_terminal_test_B prof_terminal_test_G)
      (@id
        prof_terminal_test_B
        (@fapp0
          Terminal_cat prof_terminal_test_B
          prof_terminal_test_G Terminal_obj)));

// The sole primitive boundary is a whole path of Cat-valued families.
type @prof_terminal_native_expected_path
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g prof_terminal_test_h
  prof_terminal_test_normal;

// Equality-to-arrow conversion yields one displayed map and Pi maps whole
// sections; no pointwise filler is supplied to either construction.
type @prof_terminal_native_expected_funcd
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g prof_terminal_test_h
  prof_terminal_test_normal;

type @prof_terminal_section_normalization_func
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g prof_terminal_test_h
  prof_terminal_test_normal;

constant symbol prof_terminal_test_s
  : τ (Obj (Pi_cat (@prof_terminal_native_action_catd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h)));

constant symbol prof_terminal_test_t
  : τ (Obj (Pi_cat (@prof_terminal_native_action_catd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h)));

// The normalizer retains its next hom action for recursive simplex use.
type @prof_terminal_section_normalization_next_func
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g prof_terminal_test_h
  prof_terminal_test_normal
  prof_terminal_test_s prof_terminal_test_t;

// An unrelated reflexive path at the raw terminal action is not accepted as
// evidence that this action is the identity.
constant symbol prof_terminal_test_wrong_normal
  : τ (@=
      (Hom prof_terminal_test_B
        (@fapp0
          Terminal_cat prof_terminal_test_B
          prof_terminal_test_G Terminal_obj)
        (@fapp0
          Terminal_cat prof_terminal_test_B
          prof_terminal_test_G Terminal_obj))
      (@prof_terminal_terminal_action
        prof_terminal_test_B prof_terminal_test_G)
      (@prof_terminal_terminal_action
        prof_terminal_test_B prof_terminal_test_G));

assertnot ⊢
  @prof_terminal_native_expected_path
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h
    prof_terminal_test_wrong_normal
  : τ (@=
      (Obj (@Catd_cat
        (Op_cat (Hom_cat
          prof_terminal_test_A
          prof_terminal_test_W prof_terminal_test_X))))
      (@prof_terminal_native_action_catd
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_G
        prof_terminal_test_W prof_terminal_test_X
        prof_terminal_test_g prof_terminal_test_h)
      (@prof_terminal_expected_action_catd
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_G
        prof_terminal_test_W prof_terminal_test_X
        prof_terminal_test_g prof_terminal_test_h));
