/*
  Focused reviewer for the concrete WalkingArrow--Interval free-inversion
  mapping theorem, including endpoint-sensitive and higher-action evidence.
*/

require open emdash.emdash3_2_walking_interval_universality;

// The stable unit computes on the two distinct endpoints.
assert ⊢ walking_arrow_to_interval_func
  : τ (Functor WalkingArrow_cat (Path_cat Interval_grpd));

assert ⊢
  @fapp0
    WalkingArrow_cat (Path_cat Interval_grpd)
    walking_arrow_to_interval_func walking_arrow_src
  ≡ interval_i0;

assert ⊢
  @fapp0
    WalkingArrow_cat (Path_cat Interval_grpd)
    walking_arrow_to_interval_func walking_arrow_tgt
  ≡ interval_i1;

// First-arrow computation is the selected scoped propositional observation.
assert ⊢ walking_arrow_to_interval_beta_generator
  : τ (@=
      (@= Interval_grpd interval_i0 interval_i1)
      (@fapp1_fapp0
        WalkingArrow_cat (Path_cat Interval_grpd)
        walking_arrow_to_interval_func
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      interval_seg);

// The primitive unit retains its whole join-derived presentation.
assert ⊢ walking_arrow_to_interval_join_path
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      walking_arrow_to_interval_func
      walking_arrow_to_interval_join_func);

// The naturalized cross path computes at the selected endpoint pair.
assert ⊢ walking_interval_seg_cross_func
  ≡ @Const_func
      Terminal_cat
      (Hom_cat (Path_cat Interval_grpd) interval_i0 interval_i1)
      interval_seg;

// The comparison retains one next hom action.
assert ⊢ walking_arrow_to_interval_next_func
  : τ (Functor
      (Hom_cat
        (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
        walking_arrow_generator walking_arrow_generator)
      (Hom_cat
        (Hom_cat
          (Path_cat Interval_grpd)
          interval_i0 interval_i1)
        (@fapp1_fapp0
          WalkingArrow_cat (Path_cat Interval_grpd)
          walking_arrow_to_interval_func
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@fapp1_fapp0
          WalkingArrow_cat (Path_cat Interval_grpd)
          walking_arrow_to_interval_func
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// Restriction is whole and retains endpoint-dependent generator transport.
assert [G : Grpd] ⊢ walking_interval_restrict_func G
  : τ (Functor
      (Hom_cat Grpd_cat Interval_grpd G)
      (Functor_cat WalkingArrow_cat (Path_cat G)));

assert [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G)) ⊢
  @walking_interval_restrict_i0_path G h
  : τ (@= G
      (@fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G h)
        walking_arrow_src)
      (h interval_i0));

assert [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G)) ⊢
  @walking_interval_restrict_i1_path G h
  : τ (@= G
      (@fapp0
        WalkingArrow_cat (Path_cat G)
        (@walking_interval_restrict_at G h)
        walking_arrow_tgt)
      (h interval_i1));

assert [G : Grpd]
  (h : τ (@Function_grpd Interval_grpd G)) ⊢
  @walking_interval_restrict_generator_pathover G h
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
        walking_arrow_src walking_arrow_tgt walking_arrow_generator));

// Extension computes on both endpoints and propositionally on the generator.
assert [G : Grpd] ⊢ walking_interval_extend_func G
  : τ (Functor
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (Hom_cat Grpd_cat Interval_grpd G));

assert [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G))) ⊢
  @walking_interval_extend_at G F
  ≡ @walking_interval_extend_object_function G F;

assert [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G))) ⊢
  @walking_interval_extend_beta_i0 G F
  : τ (@= G
      (@walking_interval_extend_at G F interval_i0)
      (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src));

assert [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G))) ⊢
  @walking_interval_extend_beta_i1 G F
  : τ (@= G
      (@walking_interval_extend_at G F interval_i1)
      (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt));

assert [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G))) ⊢
  @walking_interval_extend_beta_generator G F
  : τ (@=
      (@= G
        (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src)
        (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt))
      (@eq_ap
        Interval_grpd G
        (@walking_interval_extend_at G F)
        interval_i0 interval_i1 interval_seg)
      (@fapp1_fapp0
        WalkingArrow_cat (Path_cat G) F
        walking_arrow_src walking_arrow_tgt walking_arrow_generator));

assert [G : Grpd]
  [F H : τ (Functor WalkingArrow_cat (Path_cat G))]
  [eta theta : τ (@Transf WalkingArrow_cat (Path_cat G) F H)] ⊢
  @walking_interval_extend_next_func G F H eta theta
  : τ (Functor
      (Hom_cat
        (Hom_cat
          (Functor_cat WalkingArrow_cat (Path_cat G))
          F H)
        eta theta)
      (Hom_cat
        (Hom_cat
          (Hom_cat Grpd_cat Interval_grpd G)
          (@walking_interval_extend_at G F)
          (@walking_interval_extend_at G H))
        (@fapp1_fapp0
          (Functor_cat WalkingArrow_cat (Path_cat G))
          (Hom_cat Grpd_cat Interval_grpd G)
          (@walking_interval_extend_func G)
          F H eta)
        (@fapp1_fapp0
          (Functor_cat WalkingArrow_cat (Path_cat G))
          (Hom_cat Grpd_cat Interval_grpd G)
          (@walking_interval_extend_func G)
          F H theta)));

// Whole mapping-object equivalence against every groupoidal target.
assert [G : Grpd] ⊢
  @walking_interval_groupoidification_hom_omega G
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat Interval_grpd G)
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (@walking_interval_restrict_func G));

assert [G : Grpd] ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Hom_cat Grpd_cat Interval_grpd G)
    (Functor_cat WalkingArrow_cat (Path_cat G))
    (@walking_interval_restrict_func G)
    (@walking_interval_groupoidification_hom_omega G)
  ≡ @walking_interval_extend_func G;

// The self-target is a genuinely endpoint-varying consumer.
assert ⊢
  @walking_interval_extend_beta_i0
    Interval_grpd walking_arrow_to_interval_func
  : τ (@= Interval_grpd
      (@walking_interval_extend_at
        Interval_grpd walking_arrow_to_interval_func interval_i0)
      interval_i0);

assert ⊢
  @walking_interval_extend_beta_i1
    Interval_grpd walking_arrow_to_interval_func
  : τ (@= Interval_grpd
      (@walking_interval_extend_at
        Interval_grpd walking_arrow_to_interval_func interval_i1)
      interval_i1);

// Wrong target and mismatched-endpoint readings are rejected.
assertnot ⊢
  walking_interval_groupoidification_hom_omega Unit_grpd
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat Interval_grpd Nat_grpd)
      (Functor_cat WalkingArrow_cat (Path_cat Nat_grpd))
      (@walking_interval_restrict_func Nat_grpd));

assertnot ⊢
  @fapp0
    WalkingArrow_cat (Path_cat Interval_grpd)
    walking_arrow_to_interval_func walking_arrow_src
  ≡ @fapp0
      WalkingArrow_cat (Path_cat Interval_grpd)
      walking_arrow_to_interval_func walking_arrow_tgt;
