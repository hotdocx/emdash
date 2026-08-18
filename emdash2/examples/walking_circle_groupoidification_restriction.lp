/*
  Focused reviewer for the whole restriction half of the selected
  WalkingEnd--Circle groupoidification universal property.
*/

require open emdash.emdash3_2_walking_circle_restriction;

assert [G : Grpd] ⊢
  @walking_circle_restrict_func G
  : τ (Functor
      (Hom_cat Grpd_cat Circle_grpd G)
      (Functor_cat WalkingEnd_cat (Path_cat G)));

// Runtime retains the stable generic precomposition point owner.
assert [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G)) ⊢
  @walking_circle_restrict_at G h
  ≡ @hom_precomp_along_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat G)
      WalkingEnd_cat Circle_cat
      walking_to_circle_func
      (@path_map_func Circle_grpd G h);

// The stable owner has the intended literal composition reading as a path.
assert [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G)) ⊢
  @walking_circle_restrict_at_path G h
  : τ (@=
      (Functor WalkingEnd_cat (Path_cat G))
      (@walking_circle_restrict_at G h)
      (@comp_cat_fapp0
        WalkingEnd_cat Circle_cat (Path_cat G)
        (@path_map_func Circle_grpd G h)
        walking_to_circle_func));

assert [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G)) ⊢
  @walking_circle_restrict_base_path G h
  : τ (@= G
      (@fapp0
        WalkingEnd_cat (Path_cat G)
        (@walking_circle_restrict_at G h)
        walking_base)
      (h circle_base));

// The generator comparison retains its dependent endpoint transport.
assert [G : Grpd]
  (h : τ (@Function_grpd Circle_grpd G)) ⊢
  @walking_circle_restrict_loop_pathover G h
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
        circle_base circle_base circle_loop));

// The forward map remains whole and iterable on equality/higher cells.
assert [G : Grpd]
  [h k : τ (@Function_grpd Circle_grpd G)] ⊢
  @walking_circle_restrict_hom_func G h k
  : τ (Functor
      (Hom_cat
        (Hom_cat Grpd_cat Circle_grpd G)
        h k)
      (Hom_cat
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (@walking_circle_restrict_at G h)
        (@walking_circle_restrict_at G k)));

assertnot ⊢
  walking_circle_restrict_func Nat_grpd
  : τ (Functor
      (Hom_cat Grpd_cat Circle_grpd Unit_grpd)
      (Functor_cat WalkingEnd_cat (Path_cat Nat_grpd)));
