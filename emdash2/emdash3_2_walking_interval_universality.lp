/*
  Whole WalkingArrow--Interval free-inversion universality.

  Restriction along walking_arrow_to_interval_func and whole Interval
  extension are inverse on their complete mapping categories.  The two whole
  equality constants are the scoped uniqueness clauses of this concrete
  one-dimensional categorical HIT.  Their object, endpoint, generator, and
  higher readings are projections through the generic calculus.

  This is a non-endomorphism free-inversion theorem for one directed source
  shape.  It does not declare generic Groupoidify, source functoriality, or an
  adjunction.
*/

require open emdash.emdash3_2_walking_interval_extension;

// Interval uniqueness: extend_G o restrict_G = id.
constant symbol walking_interval_extend_restrict_eta_func_path
  [G : Grpd]
  : τ (@=
      (Hom
        Cat_cat
        (Hom_cat Grpd_cat Interval_grpd G)
        (Hom_cat Grpd_cat Interval_grpd G))
      (@comp_cat_fapp0
        (Hom_cat Grpd_cat Interval_grpd G)
        (Functor_cat WalkingArrow_cat (Path_cat G))
        (Hom_cat Grpd_cat Interval_grpd G)
        (@walking_interval_extend_func G)
        (@walking_interval_restrict_func G))
      (@id Cat_cat (Hom_cat Grpd_cat Interval_grpd G)));

// WalkingArrow beta: restrict_G o extend_G = id.
constant symbol walking_interval_restrict_extend_beta_func_path
  [G : Grpd]
  : τ (@=
      (Hom
        Cat_cat
        (Functor_cat WalkingArrow_cat (Path_cat G))
        (Functor_cat WalkingArrow_cat (Path_cat G)))
      (@comp_cat_fapp0
        (Functor_cat WalkingArrow_cat (Path_cat G))
        (Hom_cat Grpd_cat Interval_grpd G)
        (Functor_cat WalkingArrow_cat (Path_cat G))
        (@walking_interval_restrict_func G)
        (@walking_interval_extend_func G))
      (@id Cat_cat (Functor_cat WalkingArrow_cat (Path_cat G))));

// Fixed-forward whole mapping-object equivalence.
symbol walking_interval_groupoidification_hom_omega
  [G : Grpd]
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat Interval_grpd G)
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (@walking_interval_restrict_func G))
≔ @omega_equiv_along_intro
    Cat_cat
    (Hom_cat Grpd_cat Interval_grpd G)
    (Functor_cat WalkingArrow_cat (Path_cat G))
    (@walking_interval_restrict_func G)
    (@walking_interval_extend_func G)
    (@walking_interval_extend_func G)
    (@walking_interval_extend_restrict_eta_func_path G)
    (@walking_interval_restrict_extend_beta_func_path G);

// Object projection of Interval uniqueness.
symbol walking_interval_extend_restrict_eta_at_path
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@=
      (@Function_grpd Interval_grpd G)
      (@walking_interval_extend_at G (@walking_interval_restrict_at G h))
      h)
≔ @eq_ap
    (Hom
      Cat_cat
      (Hom_cat Grpd_cat Interval_grpd G)
      (Hom_cat Grpd_cat Interval_grpd G))
    (@Function_grpd Interval_grpd G)
    (λ K : τ (Hom
      Cat_cat
      (Hom_cat Grpd_cat Interval_grpd G)
      (Hom_cat Grpd_cat Interval_grpd G)),
      @fapp0
        (Hom_cat Grpd_cat Interval_grpd G)
        (Hom_cat Grpd_cat Interval_grpd G)
        K h)
    (@comp_cat_fapp0
      (Hom_cat Grpd_cat Interval_grpd G)
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (Hom_cat Grpd_cat Interval_grpd G)
      (@walking_interval_extend_func G)
      (@walking_interval_restrict_func G))
    (@id Cat_cat (Hom_cat Grpd_cat Interval_grpd G))
    (@walking_interval_extend_restrict_eta_func_path G);

// Endpoint projections of Interval uniqueness.
symbol walking_interval_extend_restrict_eta_i0_path
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@= G
      (@walking_interval_extend_at G (@walking_interval_restrict_at G h)
        interval_i0)
      (h interval_i0))
≔ @eq_ap
    (@Function_grpd Interval_grpd G)
    G
    (λ k : τ (@Function_grpd Interval_grpd G), k interval_i0)
    (@walking_interval_extend_at G (@walking_interval_restrict_at G h))
    h
    (@walking_interval_extend_restrict_eta_at_path G h);

symbol walking_interval_extend_restrict_eta_i1_path
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@= G
      (@walking_interval_extend_at G (@walking_interval_restrict_at G h)
        interval_i1)
      (h interval_i1))
≔ @eq_ap
    (@Function_grpd Interval_grpd G)
    G
    (λ k : τ (@Function_grpd Interval_grpd G), k interval_i1)
    (@walking_interval_extend_at G (@walking_interval_restrict_at G h))
    h
    (@walking_interval_extend_restrict_eta_at_path G h);

// Generating-path projection remains dependent over the whole function path.
symbol walking_interval_extend_restrict_eta_seg_pathover
  [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G))
  : τ (@PathOver
      (@Function_grpd Interval_grpd G)
      (λ k : τ (@Function_grpd Interval_grpd G),
        @= G (k interval_i0) (k interval_i1))
      (@walking_interval_extend_at G (@walking_interval_restrict_at G h))
      h
      (@walking_interval_extend_restrict_eta_at_path G h)
      (@eq_ap
        Interval_grpd G
        (@walking_interval_extend_at G (@walking_interval_restrict_at G h))
        interval_i0 interval_i1 interval_seg)
      (@eq_ap
        Interval_grpd G h
        interval_i0 interval_i1 interval_seg))
≔ @eq_apd
    (@Function_grpd Interval_grpd G)
    (λ k : τ (@Function_grpd Interval_grpd G),
      @= G (k interval_i0) (k interval_i1))
    (λ k : τ (@Function_grpd Interval_grpd G),
      @eq_ap Interval_grpd G k interval_i0 interval_i1 interval_seg)
    (@walking_interval_extend_at G (@walking_interval_restrict_at G h))
    h
    (@walking_interval_extend_restrict_eta_at_path G h);

// Object projection of WalkingArrow beta.
symbol walking_interval_restrict_extend_beta_at_path
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat G))
      (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
      F)
≔ @eq_ap
    (Hom
      Cat_cat
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (Functor_cat WalkingArrow_cat (Path_cat G)))
    (Functor WalkingArrow_cat (Path_cat G))
    (λ K : τ (Hom
      Cat_cat
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (Functor_cat WalkingArrow_cat (Path_cat G))),
      @fapp0
        (Functor_cat WalkingArrow_cat (Path_cat G))
        (Functor_cat WalkingArrow_cat (Path_cat G))
        K F)
    (@comp_cat_fapp0
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (Hom_cat Grpd_cat Interval_grpd G)
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (@walking_interval_restrict_func G)
      (@walking_interval_extend_func G))
    (@id Cat_cat (Functor_cat WalkingArrow_cat (Path_cat G)))
    (@walking_interval_restrict_extend_beta_func_path G);

// Endpoint projections of the WalkingArrow beta path.
symbol walking_interval_restrict_extend_beta_i0_path
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
  : τ (@= G
      (@fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
        walking_arrow_src)
      (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src))
≔ @eq_ap
    (Functor WalkingArrow_cat (Path_cat G))
    G
    (λ H : τ (Functor WalkingArrow_cat (Path_cat G)),
      @fapp0 WalkingArrow_cat (Path_cat G) H walking_arrow_src)
    (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
    F
    (@walking_interval_restrict_extend_beta_at_path G F);

symbol walking_interval_restrict_extend_beta_i1_path
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
  : τ (@= G
      (@fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
        walking_arrow_tgt)
      (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt))
≔ @eq_ap
    (Functor WalkingArrow_cat (Path_cat G))
    G
    (λ H : τ (Functor WalkingArrow_cat (Path_cat G)),
      @fapp0 WalkingArrow_cat (Path_cat G) H walking_arrow_tgt)
    (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
    F
    (@walking_interval_restrict_extend_beta_at_path G F);

// Generator projection remains dependent over the selected functor path.
symbol walking_interval_restrict_extend_beta_generator_pathover
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
  : τ (@PathOver
      (Functor WalkingArrow_cat (Path_cat G))
      (λ H : τ (Functor WalkingArrow_cat (Path_cat G)),
        @= G
          (@fapp0 WalkingArrow_cat (Path_cat G) H walking_arrow_src)
          (@fapp0 WalkingArrow_cat (Path_cat G) H walking_arrow_tgt))
      (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
      F
      (@walking_interval_restrict_extend_beta_at_path G F)
      (@fapp1_fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@fapp1_fapp0
        WalkingArrow_cat (Path_cat G) F
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_apd
    (Functor WalkingArrow_cat (Path_cat G))
    (λ H : τ (Functor WalkingArrow_cat (Path_cat G)),
      @= G
        (@fapp0 WalkingArrow_cat (Path_cat G) H walking_arrow_src)
        (@fapp0 WalkingArrow_cat (Path_cat G) H walking_arrow_tgt))
    (λ H : τ (Functor WalkingArrow_cat (Path_cat G)),
      @fapp1_fapp0
        WalkingArrow_cat (Path_cat G) H
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@walking_interval_restrict_at G (@walking_interval_extend_at G F))
    F
    (@walking_interval_restrict_extend_beta_at_path G F);
