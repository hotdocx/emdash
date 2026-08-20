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

constant symbol prof_terminal_test_p
  : τ (Hom prof_terminal_test_A
      prof_terminal_test_W prof_terminal_test_X);

constant symbol prof_terminal_test_q
  : τ (Hom prof_terminal_test_A
      prof_terminal_test_W prof_terminal_test_X);

// The directed source comparison computes at a literal old arrow while its
// off-diagonal action remains a whole functor on higher arrows.
assert ⊢
  @tapp0_fapp0
    (Hom_cat prof_terminal_test_A
      prof_terminal_test_W prof_terminal_test_X)
    (Hom_cat prof_terminal_test_B
      (@fapp0
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_W)
      (@fapp0
        Terminal_cat prof_terminal_test_B
        prof_terminal_test_G Terminal_obj))
    (@prof_terminal_expected_source_func
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g)
    (@prof_terminal_retained_source_func
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g)
    prof_terminal_test_p
    (@prof_terminal_expected_retained_source_transf
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_normal)
  ≡ @path_to_hom
      (Hom_cat prof_terminal_test_B
        (@fapp0
          prof_terminal_test_A prof_terminal_test_B
          prof_terminal_test_F prof_terminal_test_W)
        (@fapp0
          Terminal_cat prof_terminal_test_B
          prof_terminal_test_G Terminal_obj))
      (@fapp0
        (Hom_cat prof_terminal_test_A
          prof_terminal_test_W prof_terminal_test_X)
        (Hom_cat prof_terminal_test_B
          (@fapp0
            prof_terminal_test_A prof_terminal_test_B
            prof_terminal_test_F prof_terminal_test_W)
          (@fapp0
            Terminal_cat prof_terminal_test_B
            prof_terminal_test_G Terminal_obj))
        (@prof_terminal_expected_source_func
          prof_terminal_test_A prof_terminal_test_B
          prof_terminal_test_F prof_terminal_test_G
          prof_terminal_test_W prof_terminal_test_X
          prof_terminal_test_g)
        prof_terminal_test_p)
      (@fapp0
        (Hom_cat prof_terminal_test_A
          prof_terminal_test_W prof_terminal_test_X)
        (Hom_cat prof_terminal_test_B
          (@fapp0
            prof_terminal_test_A prof_terminal_test_B
            prof_terminal_test_F prof_terminal_test_W)
          (@fapp0
            Terminal_cat prof_terminal_test_B
            prof_terminal_test_G Terminal_obj))
        (@prof_terminal_retained_source_func
          prof_terminal_test_A prof_terminal_test_B
          prof_terminal_test_F prof_terminal_test_G
          prof_terminal_test_W prof_terminal_test_X
          prof_terminal_test_g)
        prof_terminal_test_p)
      (@eq_sym
        (Hom prof_terminal_test_B
          (@fapp0
            prof_terminal_test_A prof_terminal_test_B
            prof_terminal_test_F prof_terminal_test_W)
          (@fapp0
            Terminal_cat prof_terminal_test_B
            prof_terminal_test_G Terminal_obj))
        (@fapp0
          (Hom_cat prof_terminal_test_A
            prof_terminal_test_W prof_terminal_test_X)
          (Hom_cat prof_terminal_test_B
            (@fapp0
              prof_terminal_test_A prof_terminal_test_B
              prof_terminal_test_F prof_terminal_test_W)
            (@fapp0
              Terminal_cat prof_terminal_test_B
              prof_terminal_test_G Terminal_obj))
          (@prof_terminal_retained_source_func
            prof_terminal_test_A prof_terminal_test_B
            prof_terminal_test_F prof_terminal_test_G
            prof_terminal_test_W prof_terminal_test_X
            prof_terminal_test_g)
          prof_terminal_test_p)
        (@fapp0
          (Hom_cat prof_terminal_test_A
            prof_terminal_test_W prof_terminal_test_X)
          (Hom_cat prof_terminal_test_B
            (@fapp0
              prof_terminal_test_A prof_terminal_test_B
              prof_terminal_test_F prof_terminal_test_W)
            (@fapp0
              Terminal_cat prof_terminal_test_B
              prof_terminal_test_G Terminal_obj))
          (@prof_terminal_expected_source_func
            prof_terminal_test_A prof_terminal_test_B
            prof_terminal_test_F prof_terminal_test_G
            prof_terminal_test_W prof_terminal_test_X
            prof_terminal_test_g)
          prof_terminal_test_p)
        (@prof_terminal_retained_expected_source_fapp0_path
          prof_terminal_test_A prof_terminal_test_B
          prof_terminal_test_F prof_terminal_test_G
          prof_terminal_test_W prof_terminal_test_X
          prof_terminal_test_g prof_terminal_test_normal
          prof_terminal_test_p));

type @tapp1_func
  (Hom_cat prof_terminal_test_A
    prof_terminal_test_W prof_terminal_test_X)
  (Hom_cat prof_terminal_test_B
    (@fapp0
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_W)
    (@fapp0
      Terminal_cat prof_terminal_test_B
      prof_terminal_test_G Terminal_obj))
  (@prof_terminal_expected_source_func
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g)
  (@prof_terminal_retained_source_func
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g)
  prof_terminal_test_p prof_terminal_test_q
  (@prof_terminal_expected_retained_source_transf
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_normal);

// The explicit displayed normalizer computes to the rigid Hom action at each
// base object and retains its generic whole laxity/next-action tower.
assert ⊢
  @tapp0_fapp0
    (Op_cat (Hom_cat prof_terminal_test_A
      prof_terminal_test_W prof_terminal_test_X))
    Cat_cat
    (@prof_terminal_native_action_catd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h)
    (@prof_terminal_expected_action_catd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h)
    prof_terminal_test_p
    (@prof_terminal_explicit_normalization_funcd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h
      prof_terminal_test_normal)
  ≡ @prof_terminal_fibre_normalization_func
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h
      prof_terminal_test_normal prof_terminal_test_p;

constant symbol prof_terminal_test_rho
  : τ (Hom
      (Hom_cat prof_terminal_test_A
        prof_terminal_test_W prof_terminal_test_X)
      prof_terminal_test_q prof_terminal_test_p);

type @functord_laxity_transf
  (Op_cat (Hom_cat prof_terminal_test_A
    prof_terminal_test_W prof_terminal_test_X))
  (@prof_terminal_native_action_catd
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h)
  (@prof_terminal_expected_action_catd
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h)
  (@prof_terminal_explicit_normalization_funcd
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h
    prof_terminal_test_normal)
  prof_terminal_test_p prof_terminal_test_q prof_terminal_test_rho;

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

injective symbol prof_terminal_test_unrelated_component
  : τ (Hom
      (Hom_cat prof_terminal_test_B
        (@fapp0
          prof_terminal_test_A prof_terminal_test_B
          prof_terminal_test_F prof_terminal_test_W)
        (@fapp0
          Terminal_cat prof_terminal_test_B
          prof_terminal_test_G Terminal_obj))
      (@fapp0
        (Hom_cat prof_terminal_test_A
          prof_terminal_test_W prof_terminal_test_X)
        (Hom_cat prof_terminal_test_B
          (@fapp0
            prof_terminal_test_A prof_terminal_test_B
            prof_terminal_test_F prof_terminal_test_W)
          (@fapp0
            Terminal_cat prof_terminal_test_B
            prof_terminal_test_G Terminal_obj))
        (@prof_terminal_expected_source_func
          prof_terminal_test_A prof_terminal_test_B
          prof_terminal_test_F prof_terminal_test_G
          prof_terminal_test_W prof_terminal_test_X
          prof_terminal_test_g)
        prof_terminal_test_p)
      (@fapp0
        (Hom_cat prof_terminal_test_A
          prof_terminal_test_W prof_terminal_test_X)
        (Hom_cat prof_terminal_test_B
          (@fapp0
            prof_terminal_test_A prof_terminal_test_B
            prof_terminal_test_F prof_terminal_test_W)
          (@fapp0
            Terminal_cat prof_terminal_test_B
            prof_terminal_test_G Terminal_obj))
        (@prof_terminal_retained_source_func
          prof_terminal_test_A prof_terminal_test_B
          prof_terminal_test_F prof_terminal_test_G
          prof_terminal_test_W prof_terminal_test_X
          prof_terminal_test_g)
        prof_terminal_test_p));

// The component remains a directed comparison and does not collapse to an
// unrelated arrow with the same endpoints.
assertnot ⊢
  @tapp0_fapp0
    (Hom_cat prof_terminal_test_A
      prof_terminal_test_W prof_terminal_test_X)
    (Hom_cat prof_terminal_test_B
      (@fapp0
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_W)
      (@fapp0
        Terminal_cat prof_terminal_test_B
        prof_terminal_test_G Terminal_obj))
    (@prof_terminal_expected_source_func
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g)
    (@prof_terminal_retained_source_func
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g)
    prof_terminal_test_p
    (@prof_terminal_expected_retained_source_transf
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_normal)
  ≡ prof_terminal_test_unrelated_component;

// A reflexive path at the unnormalized terminal action cannot inhabit the
// normality slot of the explicit whole displayed normalizer.
assertnot ⊢
  @prof_terminal_explicit_normalization_funcd
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h
    prof_terminal_test_wrong_normal
  : τ (Functord
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

// The constructor-visible source is one whole semantic composite: first map
// the base arrow through F, then postcompose by g.
type @prof_terminal_visible_source_func
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g;

assert ⊢
  @prof_terminal_visible_source_obj
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_p
  ≡ @hom_postcomp_fapp0
      prof_terminal_test_B prof_terminal_test_B
      (@id_func prof_terminal_test_B)
      (@fapp0
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_W)
      (@fapp0
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F prof_terminal_test_X)
      (@fapp0
        Terminal_cat prof_terminal_test_B
        prof_terminal_test_G Terminal_obj)
      prof_terminal_test_g
      (@fapp1_fapp0
        prof_terminal_test_A prof_terminal_test_B
        prof_terminal_test_F
        prof_terminal_test_W prof_terminal_test_X
        prof_terminal_test_p);

// The pointwise expected/visible comparison is explicit, while the two whole
// functors remain distinct owners.
type @prof_terminal_expected_visible_source_fapp0_path
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g prof_terminal_test_p;

assertnot ⊢
  @prof_terminal_expected_source_func
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g
  ≡ @prof_terminal_visible_source_func
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g;

type @prof_terminal_visible_action_catd
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g prof_terminal_test_h;

type @prof_terminal_expected_visible_funcd
  prof_terminal_test_A prof_terminal_test_B
  prof_terminal_test_F prof_terminal_test_G
  prof_terminal_test_W prof_terminal_test_X
  prof_terminal_test_g prof_terminal_test_h;

// The whole reflag computes in one fibre through the named rigid Hom owner.
assert ⊢
  @tapp0_fapp0
    (Op_cat (Hom_cat prof_terminal_test_A
      prof_terminal_test_W prof_terminal_test_X))
    Cat_cat
    (@prof_terminal_expected_action_catd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h)
    (@prof_terminal_visible_action_catd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h)
    prof_terminal_test_p
    (@prof_terminal_expected_visible_funcd
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h)
  ≡ @prof_terminal_expected_visible_fibre_func
      prof_terminal_test_A prof_terminal_test_B
      prof_terminal_test_F prof_terminal_test_G
      prof_terminal_test_W prof_terminal_test_X
      prof_terminal_test_g prof_terminal_test_h prof_terminal_test_p;

// Another base-arrow action remains owned by the generic displayed calculus.
type @functord_laxity_transf
  (Op_cat (Hom_cat prof_terminal_test_A
    prof_terminal_test_W prof_terminal_test_X))
  (@prof_terminal_expected_action_catd
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h)
  (@prof_terminal_visible_action_catd
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h)
  (@prof_terminal_expected_visible_funcd
    prof_terminal_test_A prof_terminal_test_B
    prof_terminal_test_F prof_terminal_test_G
    prof_terminal_test_W prof_terminal_test_X
    prof_terminal_test_g prof_terminal_test_h)
  prof_terminal_test_p prof_terminal_test_q prof_terminal_test_rho;
