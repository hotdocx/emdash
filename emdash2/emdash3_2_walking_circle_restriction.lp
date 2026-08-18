/*
  Whole restriction from Circle maps to WalkingEnd representations.

  A function Circle -> G first acts through Path_cat_func and is then
  precomposed by walking_to_circle_func. Runtime retains the generic stable
  precomposition owner; a whole equality records its raw-composition reading.
  Evaluating that equality gives the base path, while dependent action gives
  the correctly transported generator comparison. No new rule or unifier is
  introduced, and the generic first hom action remains iterable.

  This is the forward half of the selected concrete groupoidification
  universal property. It does not construct the Circle extension inverse,
  beta/eta, or a generic Groupoidify reflector.
*/

require open emdash.emdash3_2_walking_circle_completion;

// Restriction along WalkingEnd -> Circle, whole in the Circle function.
symbol walking_circle_restrict_func
  (G : Grpd)
  : τ (Functor
      (Hom_cat Grpd_cat Circle_grpd G)
      (Functor_cat WalkingEnd_cat (Path_cat G)))
≔ @comp_cat_fapp0
    (Hom_cat Grpd_cat Circle_grpd G)
    (Functor_cat Circle_cat (Path_cat G))
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (@comp_cat_con_func
      WalkingEnd_cat Circle_cat (Path_cat G)
      walking_to_circle_func)
    (@fapp1_func
      Grpd_cat Cat_cat Path_cat_func
      Circle_grpd G);

// Selected WalkingEnd representation obtained by restriction.
symbol walking_circle_restrict_at
  [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G))
  : τ (Functor WalkingEnd_cat (Path_cat G))
≔ @fapp0
    (Hom_cat Grpd_cat Circle_grpd G)
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (@walking_circle_restrict_func G)
    h;

// Whole proof-time comparison with literal categorical composition.
symbol walking_circle_restrict_at_path
  [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G))
  : τ (@=
      (Functor WalkingEnd_cat (Path_cat G))
      (@walking_circle_restrict_at G h)
      (@comp_cat_fapp0
        WalkingEnd_cat Circle_cat (Path_cat G)
        (@path_map_func Circle_grpd G h)
        walking_to_circle_func))
≔ @eq_refl
    (Functor WalkingEnd_cat (Path_cat G))
    (@hom_precomp_along_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat G)
      WalkingEnd_cat Circle_cat
      walking_to_circle_func
      (@path_map_func Circle_grpd G h));

// Base observation obtained by evaluating the whole functor comparison.
symbol walking_circle_restrict_base_path
  [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G))
  : τ (@= G
      (@fapp0
        WalkingEnd_cat (Path_cat G)
        (@walking_circle_restrict_at G h)
        walking_base)
      (h circle_base))
≔ @eq_ap
    (Functor WalkingEnd_cat (Path_cat G))
    G
    (λ F : τ (Functor WalkingEnd_cat (Path_cat G)),
      @fapp0 WalkingEnd_cat (Path_cat G) F walking_base)
    (@walking_circle_restrict_at G h)
    (@comp_cat_fapp0
      WalkingEnd_cat Circle_cat (Path_cat G)
      (@path_map_func Circle_grpd G h)
      walking_to_circle_func)
    (@walking_circle_restrict_at_path G h);

/*
  Generator observation over the whole functor path.

  The loop classifier depends on the functor's base image, so ordinary
  homogeneous equality would erase necessary endpoint transport. Dependent
  action produces the canonical PathOver, whose target computes to ap(h,loop).
*/
symbol walking_circle_restrict_loop_pathover
  [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G))
  : τ (@PathOver
      (Functor WalkingEnd_cat (Path_cat G))
      (λ F : τ (Functor WalkingEnd_cat (Path_cat G)),
        @= G
          (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base)
          (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base))
      (@walking_circle_restrict_at G h)
      (@comp_cat_fapp0
        WalkingEnd_cat Circle_cat (Path_cat G)
        (@path_map_func Circle_grpd G h)
        walking_to_circle_func)
      (@walking_circle_restrict_at_path G h)
      (@fapp1_fapp0
        WalkingEnd_cat (Path_cat G)
        (@walking_circle_restrict_at G h)
        walking_base walking_base walking_loop)
      (@eq_ap Circle_grpd G h
        circle_base circle_base circle_loop))
≔ @eq_apd
    (Functor WalkingEnd_cat (Path_cat G))
    (λ F : τ (Functor WalkingEnd_cat (Path_cat G)),
      @= G
        (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base)
        (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base))
    (λ F : τ (Functor WalkingEnd_cat (Path_cat G)),
      @fapp1_fapp0
        WalkingEnd_cat (Path_cat G) F
        walking_base walking_base walking_loop)
    (@walking_circle_restrict_at G h)
    (@comp_cat_fapp0
      WalkingEnd_cat Circle_cat (Path_cat G)
      (@path_map_func Circle_grpd G h)
      walking_to_circle_func)
    (@walking_circle_restrict_at_path G h);

// Retained first hom action of whole restriction.
symbol walking_circle_restrict_hom_func
  [G : Grpd]
  [h k : τ (@Function_grpd Circle_grpd G)]
  : τ (Functor
      (Hom_cat
        (Hom_cat Grpd_cat Circle_grpd G)
        h k)
      (Hom_cat
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (@walking_circle_restrict_at G h)
        (@walking_circle_restrict_at G k)))
≔ @fapp1_func
    (Hom_cat Grpd_cat Circle_grpd G)
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (@walking_circle_restrict_func G)
    h k;
