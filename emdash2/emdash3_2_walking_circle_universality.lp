/*
  Whole WalkingEnd--Circle groupoidification universality.

  Restriction along walking_to_circle_func and the whole Circle extension are
  inverse on their complete mapping categories.  The two whole equality
  constants below are the scoped uniqueness clauses of these one-dimensional
  categorical HITs: Circle uniqueness after extending restricted data, and
  WalkingEnd beta after restricting an extension.  They are not runtime
  folds.  All point, generator, transformation, and higher-action readings
  are projections from those whole owners and the existing generic calculus.

  The resulting fixed-forward OmegaEquivAlong is the selected concrete
  groupoidification theorem.  It does not declare a generic Groupoidify
  reflector or adjunction.  No rule or unifier is introduced, and Circle loop
  computation remains propositional under the active HIT policy.
*/

require open emdash.emdash3_2_walking_circle_extension;

/*
  Circle uniqueness:

    extend_G o restrict_G = id.

  At an object h, both sides are Circle functions.  The clause is whole in h,
  so its generic hom action also carries transformations and all higher cells.
*/
constant symbol walking_circle_extend_restrict_eta_func_path
  [G : Grpd]
  : τ (@=
      (Hom
        Cat_cat
        (Hom_cat Grpd_cat Circle_grpd G)
        (Hom_cat Grpd_cat Circle_grpd G))
      (@comp_cat_fapp0
        (Hom_cat Grpd_cat Circle_grpd G)
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (Hom_cat Grpd_cat Circle_grpd G)
        (@walking_circle_extend_func G)
        (@walking_circle_restrict_func G))
      (@id Cat_cat (Hom_cat Grpd_cat Circle_grpd G)));

/*
  WalkingEnd beta:

    restrict_G o extend_G = id.

  Its object projection recovers an arbitrary representation, not merely the
  selected base and loop after erasing whole functorial action.
*/
constant symbol walking_circle_restrict_extend_beta_func_path
  [G : Grpd]
  : τ (@=
      (Hom
        Cat_cat
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (Functor_cat WalkingEnd_cat (Path_cat G)))
      (@comp_cat_fapp0
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (Hom_cat Grpd_cat Circle_grpd G)
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (@walking_circle_restrict_func G)
        (@walking_circle_extend_func G))
      (@id Cat_cat (Functor_cat WalkingEnd_cat (Path_cat G))));

// Fixed-forward whole mapping-object equivalence.
symbol walking_circle_groupoidification_hom_omega
  [G : Grpd]
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat Circle_grpd G)
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (@walking_circle_restrict_func G))
≔ @omega_equiv_along_intro
    Cat_cat
    (Hom_cat Grpd_cat Circle_grpd G)
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (@walking_circle_restrict_func G)
    (@walking_circle_extend_func G)
    (@walking_circle_extend_func G)
    (@walking_circle_extend_restrict_eta_func_path G)
    (@walking_circle_restrict_extend_beta_func_path G);

// Object projection of Circle uniqueness.
symbol walking_circle_extend_restrict_eta_at_path
  [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G))
  : τ (@=
      (@Function_grpd Circle_grpd G)
      (@walking_circle_extend_at G (@walking_circle_restrict_at G h))
      h)
≔ @eq_ap
    (Hom
      Cat_cat
      (Hom_cat Grpd_cat Circle_grpd G)
      (Hom_cat Grpd_cat Circle_grpd G))
    (@Function_grpd Circle_grpd G)
    (λ K : τ (Hom
      Cat_cat
      (Hom_cat Grpd_cat Circle_grpd G)
      (Hom_cat Grpd_cat Circle_grpd G)),
      @fapp0
        (Hom_cat Grpd_cat Circle_grpd G)
        (Hom_cat Grpd_cat Circle_grpd G)
        K h)
    (@comp_cat_fapp0
      (Hom_cat Grpd_cat Circle_grpd G)
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (Hom_cat Grpd_cat Circle_grpd G)
      (@walking_circle_extend_func G)
      (@walking_circle_restrict_func G))
    (@id Cat_cat (Hom_cat Grpd_cat Circle_grpd G))
    (@walking_circle_extend_restrict_eta_func_path G);

// Point projection of Circle uniqueness.
symbol walking_circle_extend_restrict_eta_base_path
  [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G))
  : τ (@= G
      (@walking_circle_extend_at G (@walking_circle_restrict_at G h)
        circle_base)
      (h circle_base))
≔ @eq_ap
    (@Function_grpd Circle_grpd G)
    G
    (λ k : τ (@Function_grpd Circle_grpd G), k circle_base)
    (@walking_circle_extend_at G (@walking_circle_restrict_at G h))
    h
    (@walking_circle_extend_restrict_eta_at_path G h);

/*
  Loop projection is dependent over the whole Circle-function path. It needs
  no ordinary circle_rec/eq_ap computation: eq_apd retains the required
  endpoint transport while the whole uniqueness clause owns the comparison.
  The selected Circle-induction PathOver constructor beta is independently
  judgmental.
*/
symbol walking_circle_extend_restrict_eta_loop_pathover
  [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G))
  : τ (@PathOver
      (@Function_grpd Circle_grpd G)
      (λ k : τ (@Function_grpd Circle_grpd G),
        @= G (k circle_base) (k circle_base))
      (@walking_circle_extend_at G (@walking_circle_restrict_at G h))
      h
      (@walking_circle_extend_restrict_eta_at_path G h)
      (@eq_ap
        Circle_grpd G
        (@walking_circle_extend_at G (@walking_circle_restrict_at G h))
        circle_base circle_base circle_loop)
      (@eq_ap
        Circle_grpd G h
        circle_base circle_base circle_loop))
≔ @eq_apd
    (@Function_grpd Circle_grpd G)
    (λ k : τ (@Function_grpd Circle_grpd G),
      @= G (k circle_base) (k circle_base))
    (λ k : τ (@Function_grpd Circle_grpd G),
      @eq_ap Circle_grpd G k circle_base circle_base circle_loop)
    (@walking_circle_extend_at G (@walking_circle_restrict_at G h))
    h
    (@walking_circle_extend_restrict_eta_at_path G h);

// Object projection of WalkingEnd beta.
symbol walking_circle_restrict_extend_beta_at_path
  [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G)))
  : τ (@=
      (Functor WalkingEnd_cat (Path_cat G))
      (@walking_circle_restrict_at G (@walking_circle_extend_at G F))
      F)
≔ @eq_ap
    (Hom
      Cat_cat
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (Functor_cat WalkingEnd_cat (Path_cat G)))
    (Functor WalkingEnd_cat (Path_cat G))
    (λ K : τ (Hom
      Cat_cat
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (Functor_cat WalkingEnd_cat (Path_cat G))),
      @fapp0
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (Functor_cat WalkingEnd_cat (Path_cat G))
        K F)
    (@comp_cat_fapp0
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (Hom_cat Grpd_cat Circle_grpd G)
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (@walking_circle_restrict_func G)
      (@walking_circle_extend_func G))
    (@id Cat_cat (Functor_cat WalkingEnd_cat (Path_cat G)))
    (@walking_circle_restrict_extend_beta_func_path G);

// Base projection of the WalkingEnd beta path.
symbol walking_circle_restrict_extend_beta_base_path
  [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G)))
  : τ (@= G
      (@fapp0
        WalkingEnd_cat (Path_cat G)
        (@walking_circle_restrict_at G (@walking_circle_extend_at G F))
        walking_base)
      (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base))
≔ @eq_ap
    (Functor WalkingEnd_cat (Path_cat G))
    G
    (λ H : τ (Functor WalkingEnd_cat (Path_cat G)),
      @fapp0 WalkingEnd_cat (Path_cat G) H walking_base)
    (@walking_circle_restrict_at G (@walking_circle_extend_at G F))
    F
    (@walking_circle_restrict_extend_beta_at_path G F);

// Generator projection remains dependent over the selected functor path.
symbol walking_circle_restrict_extend_beta_loop_pathover
  [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G)))
  : τ (@PathOver
      (Functor WalkingEnd_cat (Path_cat G))
      (λ H : τ (Functor WalkingEnd_cat (Path_cat G)),
        @= G
          (@fapp0 WalkingEnd_cat (Path_cat G) H walking_base)
          (@fapp0 WalkingEnd_cat (Path_cat G) H walking_base))
      (@walking_circle_restrict_at G (@walking_circle_extend_at G F))
      F
      (@walking_circle_restrict_extend_beta_at_path G F)
      (@fapp1_fapp0
        WalkingEnd_cat (Path_cat G)
        (@walking_circle_restrict_at G (@walking_circle_extend_at G F))
        walking_base walking_base walking_loop)
      (@fapp1_fapp0
        WalkingEnd_cat (Path_cat G) F
        walking_base walking_base walking_loop))
≔ @eq_apd
    (Functor WalkingEnd_cat (Path_cat G))
    (λ H : τ (Functor WalkingEnd_cat (Path_cat G)),
      @= G
        (@fapp0 WalkingEnd_cat (Path_cat G) H walking_base)
        (@fapp0 WalkingEnd_cat (Path_cat G) H walking_base))
    (λ H : τ (Functor WalkingEnd_cat (Path_cat G)),
      @fapp1_fapp0
        WalkingEnd_cat (Path_cat G) H
        walking_base walking_base walking_loop)
    (@walking_circle_restrict_at G (@walking_circle_extend_at G F))
    F
    (@walking_circle_restrict_extend_beta_at_path G F);
