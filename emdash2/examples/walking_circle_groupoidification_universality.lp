/*
  Focused reviewer for whole WalkingEnd--Circle groupoidification
  universality against an arbitrary groupoidal target.
*/

require open emdash.emdash3_2_walking_circle_universality;

assert [G : Grpd] ⊢
  @walking_circle_extend_restrict_eta_func_path G
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

assert [G : Grpd] ⊢
  @walking_circle_restrict_extend_beta_func_path G
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

assert [G : Grpd] ⊢
  @walking_circle_groupoidification_hom_omega G
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat Circle_grpd G)
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (@walking_circle_restrict_func G));

assert [G : Grpd] ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Hom_cat Grpd_cat Circle_grpd G)
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (@walking_circle_restrict_func G)
    (@walking_circle_groupoidification_hom_omega G)
  ≡ @walking_circle_extend_func G;

assert [G : Grpd] ⊢
  @omega_equiv_along_right_inv
    Cat_cat
    (Hom_cat Grpd_cat Circle_grpd G)
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (@walking_circle_restrict_func G)
    (@walking_circle_groupoidification_hom_omega G)
  ≡ @walking_circle_extend_func G;

assert [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G)) ⊢
  @walking_circle_extend_restrict_eta_base_path G h
  : τ (@= G
      (@walking_circle_extend_at G (@walking_circle_restrict_at G h)
        circle_base)
      (h circle_base));

assert [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G)) ⊢
  @walking_circle_extend_restrict_eta_loop_pathover G h
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
      (@eq_ap Circle_grpd G h
        circle_base circle_base circle_loop));

assert [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G))) ⊢
  @walking_circle_restrict_extend_beta_base_path G F
  : τ (@= G
      (@fapp0
        WalkingEnd_cat (Path_cat G)
        (@walking_circle_restrict_at G (@walking_circle_extend_at G F))
        walking_base)
      (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base));

assert [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G))) ⊢
  @walking_circle_restrict_extend_beta_loop_pathover G F
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
        walking_base walking_base walking_loop));

assert [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))] ⊢
  @fapp1_func
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (Hom_cat Grpd_cat Circle_grpd G)
    (@omega_equiv_along_left_inv
      Cat_cat
      (Hom_cat Grpd_cat Circle_grpd G)
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (@walking_circle_restrict_func G)
      (@walking_circle_groupoidification_hom_omega G))
    F H
  ≡ @walking_circle_extend_hom_func G F H;

assert [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  [eta theta : τ (@Transf WalkingEnd_cat (Path_cat G) F H)] ⊢
  @fapp1_func
    (Hom_cat
      (Functor_cat WalkingEnd_cat (Path_cat G))
      F H)
    (Hom_cat
      (Hom_cat Grpd_cat Circle_grpd G)
      (@walking_circle_extend_at G F)
      (@walking_circle_extend_at G H))
    (@fapp1_func
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (Hom_cat Grpd_cat Circle_grpd G)
      (@omega_equiv_along_right_inv
        Cat_cat
        (Hom_cat Grpd_cat Circle_grpd G)
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (@walking_circle_restrict_func G)
        (@walking_circle_groupoidification_hom_omega G))
      F H)
    eta theta
  ≡ @walking_circle_extend_next_func G F H eta theta;

assertnot ⊢
  walking_circle_groupoidification_hom_omega Unit_grpd
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Grpd_cat Circle_grpd Nat_grpd)
      (Functor_cat WalkingEnd_cat (Path_cat Nat_grpd))
      (@walking_circle_restrict_func Nat_grpd));
