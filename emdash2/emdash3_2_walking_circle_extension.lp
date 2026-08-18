/*
  Whole Circle extension of WalkingEnd representations in a path category.

  Object action is ordinary Circle recursion on the image of walking_base and
  walking_loop. A transformation into Path_cat(G) is pointwise an equivalence;
  the existing strict pointwise-to-whole assembly and category univalence
  therefore give a path between the whole representations. Applying the
  object extension function to that path gives the semantic path between the
  resulting Circle functions.

  The primitive whole functor is the narrow categorical-HIT recursor owner
  missing from the object-only Circle interface. Its object beta computes at
  runtime. Its first-arrow beta remains propositional, like the Circle loop
  beta itself, while generic fapp1_func retains an iterable next action. No
  new generic groupoidification reflector, identity/composition rule, or
  unifier is introduced.
*/

require open emdash.emdash3_2_walking_circle_restriction;
require open emdash.emdash3_2_strict_pointwise_equivalences;

// Extend the base object and generator of F by ordinary Circle recursion.
symbol walking_circle_extend_object_function
  (G : Grpd)
  : τ (@Function_grpd
      (Functor WalkingEnd_cat (Path_cat G))
      (@Function_grpd Circle_grpd G))
≔ λ F : τ (Functor WalkingEnd_cat (Path_cat G)),
    λ x : τ Circle_grpd,
      @circle_rec
        G
        (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base)
        (@fapp1_fapp0
          WalkingEnd_cat (Path_cat G) F
          walking_base walking_base walking_loop)
        x;

// Components in Path_cat(G) carry canonical equality-valued equivalences.
symbol walking_circle_transf_pointwise_omega
  [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  (eta : τ (@Transf WalkingEnd_cat (Path_cat G) F H))
  : τ (@StrictTransfPointwiseOmegaAlong
      WalkingEnd_cat (Path_cat G) F H eta)
≔ λ x : τ (Obj WalkingEnd_cat),
    @path_equiv_along
      G
      (@fapp0 WalkingEnd_cat (Path_cat G) F x)
      (@fapp0 WalkingEnd_cat (Path_cat G) H x)
      (@tapp0_fapp0
        WalkingEnd_cat (Path_cat G) F H x eta);

// Pointwise equivalence plus functor-category univalence gives F = H.
symbol walking_circle_representation_path
  [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  (eta : τ (@Transf WalkingEnd_cat (Path_cat G) F H))
  : τ (@=
      (Functor WalkingEnd_cat (Path_cat G))
      F H)
≔ @strict_transf_pointwise_path
    WalkingEnd_cat (Path_cat G) F H eta
    (@walking_circle_transf_pointwise_omega G F H eta);

// Semantic first-arrow action of extension on a whole transformation.
symbol walking_circle_extend_transf_path
  [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  (eta : τ (@Transf WalkingEnd_cat (Path_cat G) F H))
  : τ (@=
      (@Function_grpd Circle_grpd G)
      (walking_circle_extend_object_function G F)
      (walking_circle_extend_object_function G H))
≔ @eq_ap
    (Functor WalkingEnd_cat (Path_cat G))
    (@Function_grpd Circle_grpd G)
    (@walking_circle_extend_object_function G)
    F H
    (@walking_circle_representation_path G F H eta);

// Whole categorical-HIT recursor, functorial in the WalkingEnd representation.
injective symbol walking_circle_extend_func
  (G : Grpd)
  : τ (Functor
      (Functor_cat WalkingEnd_cat (Path_cat G))
      (Hom_cat Grpd_cat Circle_grpd G));

// Runtime object beta selects the deployed Circle recursor.
rule @fapp0 _ _ (@walking_circle_extend_func $G) $F
  ↪ @walking_circle_extend_object_function $G $F;

// Selected Circle function obtained from one WalkingEnd representation.
symbol walking_circle_extend_at
  [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G)))
  : τ (@Function_grpd Circle_grpd G)
≔ @fapp0
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (Hom_cat Grpd_cat Circle_grpd G)
    (@walking_circle_extend_func G)
    F;

// Point-constructor beta of the selected extension.
symbol walking_circle_extend_beta_base
  [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G)))
  : τ (@= G
      (@walking_circle_extend_at G F circle_base)
      (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base))
≔ @eq_refl
    G
    (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base);

// Propositional loop-constructor beta inherited from Circle recursion.
symbol walking_circle_extend_beta_loop
  [G : Grpd]
  (F : τ (Functor WalkingEnd_cat (Path_cat G)))
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
        walking_base walking_base walking_loop))
≔ @circle_rec_beta_loop_path
    G
    (@fapp0 WalkingEnd_cat (Path_cat G) F walking_base)
    (@fapp1_fapp0
      WalkingEnd_cat (Path_cat G) F
      walking_base walking_base walking_loop);

// The generic first hom action remains a whole functor.
symbol walking_circle_extend_hom_func
  [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  : τ (Functor
      (Hom_cat
        (Functor_cat WalkingEnd_cat (Path_cat G))
        F H)
      (Hom_cat
        (Hom_cat Grpd_cat Circle_grpd G)
        (@walking_circle_extend_at G F)
        (@walking_circle_extend_at G H)))
≔ @fapp1_func
    (Functor_cat WalkingEnd_cat (Path_cat G))
    (Hom_cat Grpd_cat Circle_grpd G)
    (@walking_circle_extend_func G)
    F H;

/*
  First-arrow computation of the whole categorical-HIT recursor.

  This is propositional signature data rather than a competing fapp1 runtime
  rule. Generic functoriality retains identity/composition and all higher
  action; the semantic comparison is the pointwise-univalence path above.
*/
constant symbol walking_circle_extend_transf_agrees
  [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  (eta : τ (@Transf WalkingEnd_cat (Path_cat G) F H))
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

// One retained higher action of the whole extension owner.
symbol walking_circle_extend_next_func
  [G : Grpd]
  [F H : τ (Functor WalkingEnd_cat (Path_cat G))]
  [eta theta : τ (@Transf WalkingEnd_cat (Path_cat G) F H)]
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
          F H theta)))
≔ @fapp1_func
    (Hom_cat
      (Functor_cat WalkingEnd_cat (Path_cat G))
      F H)
    (Hom_cat
      (Hom_cat Grpd_cat Circle_grpd G)
      (@walking_circle_extend_at G F)
      (@walking_circle_extend_at G H))
    (@walking_circle_extend_hom_func G F H)
    eta theta;
