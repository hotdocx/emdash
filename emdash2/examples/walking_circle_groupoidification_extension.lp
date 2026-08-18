/*
  Focused reviewer for the whole Circle extension of WalkingEnd
  representations into a path category.
*/

require open emdash.emdash3_2_walking_circle_extension;

assert [G : Grpd] ⊢
  @walking_circle_extend_func G
  : τ (Functor
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (Hom_cat Grpd_cat Circle_grpd G));

assert [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G))) ⊢
  @walking_circle_extend_at G F
  ≡ @walking_circle_extend_object_function G F;

assert [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G))) ⊢
  @walking_circle_extend_beta_base G F
  : τ (@= G
      (@walking_circle_extend_at G F circle_base)
      (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base));

assert [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G))) ⊢
  @walking_circle_extend_beta_loop G F
  : τ (@=
      (@= G
        (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base)
        (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base))
      (@eq_ap
        Circle_grpd G
        (@walking_circle_extend_at G F)
        circle_base circle_base circle_loop)
      (@fapp1_fapp0
        WalkingEnd_cat (Path_cat G) F
        walking_base walking_base walking_loop));

assert [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  (eta : τ (@Transf WalkingEnd_cat (Path_cat G) F H)) ⊢
  @walking_circle_transf_pointwise_omega G F H eta
  : τ (@StrictTransfPointwiseOmegaAlong
      WalkingEnd_cat (Path_cat G) F H eta);

assert [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  (eta : τ (@Transf WalkingEnd_cat (Path_cat G) F H)) ⊢
  @walking_circle_representation_path G F H eta
  : τ (@=
      (Functor WalkingEnd_cat (Path_cat G))
      F H);

assert [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  (eta : τ (@Transf WalkingEnd_cat (Path_cat G) F H)) ⊢
  @walking_circle_extend_transf_agrees G F H eta
  : τ (@=
      (@= (@Function_grpd Circle_grpd G)
        (@walking_circle_extend_at G F)
        (@walking_circle_extend_at G H))
      (@fapp1_fapp0
        (Functor_cat WalkingEnd_cat (Path_cat G))
        (Hom_cat Grpd_cat Circle_grpd G)
        (@walking_circle_extend_func G)
        F H eta)
      (@walking_circle_extend_transf_path G F H eta));

// The first hom owner remains iterable one dimension higher.
assert [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  [eta theta : τ (@Transf WalkingEnd_cat (Path_cat G) F H)] ⊢
  @walking_circle_extend_next_func G F H eta theta
  : τ (Functor
      (Hom_cat
        (Hom_cat
          (Functor_cat WalkingEnd_cat (Path_cat G))
          F H)
        eta theta)
      (Hom_cat
        (Hom_cat
          (Hom_cat Grpd_cat Circle_grpd G)
          (@walking_circle_extend_at G F)
          (@walking_circle_extend_at G H))
        (@fapp1_fapp0
          (Functor_cat WalkingEnd_cat (Path_cat G))
          (Hom_cat Grpd_cat Circle_grpd G)
          (@walking_circle_extend_func G)
          F H eta)
        (@fapp1_fapp0
          (Functor_cat WalkingEnd_cat (Path_cat G))
          (Hom_cat Grpd_cat Circle_grpd G)
          (@walking_circle_extend_func G)
          F H theta)));

assertnot ⊢
  walking_circle_extend_func Nat_grpd
  : τ (Functor
      (Functor_cat WalkingEnd_cat (Path_cat Unit_grpd))
      (Hom_cat Grpd_cat Circle_grpd Nat_grpd));
