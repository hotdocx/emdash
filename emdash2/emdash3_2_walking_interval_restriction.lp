/*
  Whole restriction from Interval maps to WalkingArrow representations.

  A function Interval -> G acts through Path_cat_func and is precomposed by
  walking_arrow_to_interval_func.  The construction is transparent and keeps
  the generic hom action iterable.  Endpoint observations are projections of
  one whole comparison with literal categorical composition.
*/

require open emdash.emdash3_2_walking_interval_comparison;

// Restriction along WalkingArrow -> Path(Interval), whole in the function.
symbol walking_interval_restrict_func
  (G : Grpd)
  : τ (Functor
      (Hom_cat Grpd_cat Interval_grpd G)
      (Functor_cat WalkingArrow_cat (Path_cat G)))
≔ @comp_cat_fapp0
    (Hom_cat Grpd_cat Interval_grpd G)
    (Functor_cat (Path_cat Interval_grpd) (Path_cat G))
    (Functor_cat WalkingArrow_cat (Path_cat G))
    (@comp_cat_con_func
      WalkingArrow_cat (Path_cat Interval_grpd) (Path_cat G)
      walking_arrow_to_interval_func)
    (@fapp1_func
      Grpd_cat Cat_cat Path_cat_func
      Interval_grpd G);

// Representation selected by restricting one interval function.
symbol walking_interval_restrict_at
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (Functor WalkingArrow_cat (Path_cat G))
≔ @fapp0
    (Hom_cat Grpd_cat Interval_grpd G)
    (Functor_cat WalkingArrow_cat (Path_cat G))
    (@walking_interval_restrict_func G)
    h;

// Whole proof-time comparison with literal categorical composition.
symbol walking_interval_restrict_at_path
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat G))
      (@walking_interval_restrict_at G h)
      (@comp_cat_fapp0
        WalkingArrow_cat (Path_cat Interval_grpd) (Path_cat G)
        (@path_map_func Interval_grpd G h)
        walking_arrow_to_interval_func))
≔ @eq_refl
    (Functor WalkingArrow_cat (Path_cat G))
    (@hom_precomp_along_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat G)
      WalkingArrow_cat (Path_cat Interval_grpd)
      walking_arrow_to_interval_func
      (@path_map_func Interval_grpd G h));

// Endpoint projections of the whole functor comparison.
symbol walking_interval_restrict_i0_path
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@= G
      (@fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G h)
        walking_arrow_src)
      (h interval_i0))
≔ @eq_ap
    (Functor WalkingArrow_cat (Path_cat G))
    G
    (λ F : τ (Functor WalkingArrow_cat (Path_cat G)),
      @fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src)
    (@walking_interval_restrict_at G h)
    (@comp_cat_fapp0
      WalkingArrow_cat (Path_cat Interval_grpd) (Path_cat G)
      (@path_map_func Interval_grpd G h)
      walking_arrow_to_interval_func)
    (@walking_interval_restrict_at_path G h);

symbol walking_interval_restrict_i1_path
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@= G
      (@fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G h)
        walking_arrow_tgt)
      (h interval_i1))
≔ @eq_ap
    (Functor WalkingArrow_cat (Path_cat G))
    G
    (λ F : τ (Functor WalkingArrow_cat (Path_cat G)),
      @fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt)
    (@walking_interval_restrict_at G h)
    (@comp_cat_fapp0
      WalkingArrow_cat (Path_cat Interval_grpd) (Path_cat G)
      (@path_map_func Interval_grpd G h)
      walking_arrow_to_interval_func)
    (@walking_interval_restrict_at_path G h);

/*
  Generator projection is dependent over the whole functor path.  Its target
  deliberately retains the literal composite's first-arrow action; the
  separate unit-generator path and ordinary eq_ap action compare that target
  with eq_ap(h,interval_seg) without erasing endpoint transport.
*/
symbol walking_interval_restrict_generator_pathover
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@PathOver
      (Functor WalkingArrow_cat (Path_cat G))
      (λ F : τ (Functor WalkingArrow_cat (Path_cat G)),
        @= G
          (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src)
          (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt))
      (@walking_interval_restrict_at G h)
      (@comp_cat_fapp0
        WalkingArrow_cat (Path_cat Interval_grpd) (Path_cat G)
        (@path_map_func Interval_grpd G h)
        walking_arrow_to_interval_func)
      (@walking_interval_restrict_at_path G h)
      (@fapp1_fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G h)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@fapp1_fapp0
        WalkingArrow_cat (Path_cat G)
        (@comp_cat_fapp0
          WalkingArrow_cat (Path_cat Interval_grpd) (Path_cat G)
          (@path_map_func Interval_grpd G h)
          walking_arrow_to_interval_func)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_apd
    (Functor WalkingArrow_cat (Path_cat G))
    (λ F : τ (Functor WalkingArrow_cat (Path_cat G)),
      @= G
        (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src)
        (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt))
    (λ F : τ (Functor WalkingArrow_cat (Path_cat G)),
      @fapp1_fapp0
        WalkingArrow_cat (Path_cat G) F
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@walking_interval_restrict_at G h)
    (@comp_cat_fapp0
      WalkingArrow_cat (Path_cat Interval_grpd) (Path_cat G)
      (@path_map_func Interval_grpd G h)
      walking_arrow_to_interval_func)
    (@walking_interval_restrict_at_path G h);

// Retained first hom action of whole restriction.
symbol walking_interval_restrict_hom_func
  [G : Grpd]
  [h k : τ (@Function_grpd Interval_grpd G)]
  : τ (Functor
      (Hom_cat
        (Hom_cat Grpd_cat Interval_grpd G)
        h k)
      (Hom_cat
        (Functor_cat WalkingArrow_cat (Path_cat G))
        (@walking_interval_restrict_at G h)
        (@walking_interval_restrict_at G k)))
≔ @fapp1_func
    (Hom_cat Grpd_cat Interval_grpd G)
    (Functor_cat WalkingArrow_cat (Path_cat G))
    (@walking_interval_restrict_func G)
    h k;
