/*
  Whole Interval extension of WalkingArrow representations in a path category.

  Object action uses interval_rec on the two endpoint images and the selected
  directed generator.  A transformation into Path_cat(G) is pointwise an
  equivalence; strict pointwise-to-whole assembly therefore gives a path
  between representations, and ordinary equality action supplies the semantic
  first-arrow action of extension.

  The primitive whole functor is the narrow categorical-HIT recursor owner.
  Its object action computes; generic fapp1_func retains the higher action.
*/

require open emdash.emdash3_2_walking_interval_restriction;
require open emdash.emdash3_2_strict_pointwise_equivalences;

// Extend endpoint and generator data by ordinary Interval recursion.
symbol walking_interval_extend_object_function
  (G : Grpd)
  : τ (@Function_grpd
      (Functor WalkingArrow_cat (Path_cat G))
      (@Function_grpd Interval_grpd G))
≔ λ F : τ (Functor WalkingArrow_cat (Path_cat G)),
    λ x : τ Interval_grpd,
      @interval_rec
        G
        (@fapp0
          WalkingArrow_cat (Path_cat G) F walking_arrow_src)
        (@fapp0
          WalkingArrow_cat (Path_cat G) F walking_arrow_tgt)
        (@fapp1_fapp0
          WalkingArrow_cat (Path_cat G) F
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        x;

// Components in Path_cat(G) carry canonical equality-valued equivalences.
symbol walking_interval_transf_pointwise_omega
  [G : Grpd]
  [F H : τ (Functor WalkingArrow_cat (Path_cat G))]
  (eta : τ (@Transf WalkingArrow_cat (Path_cat G) F H))
  : τ (@StrictTransfPointwiseOmegaAlong
      WalkingArrow_cat (Path_cat G) F H eta)
≔ λ x : τ (Obj WalkingArrow_cat),
    @path_equiv_along
      G
      (@fapp0 WalkingArrow_cat (Path_cat G) F x)
      (@fapp0 WalkingArrow_cat (Path_cat G) H x)
      (@tapp0_fapp0
        WalkingArrow_cat (Path_cat G) F H x eta);

// Pointwise equivalence plus functor-category univalence gives F = H.
symbol walking_interval_representation_path
  [G : Grpd]
  [F H : τ (Functor WalkingArrow_cat (Path_cat G))]
  (eta : τ (@Transf WalkingArrow_cat (Path_cat G) F H))
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat G))
      F H)
≔ @strict_transf_pointwise_path
    WalkingArrow_cat (Path_cat G) F H eta
    (@walking_interval_transf_pointwise_omega G F H eta);

// Semantic first-arrow action of extension on a whole transformation.
symbol walking_interval_extend_transf_path
  [G : Grpd]
  [F H : τ (Functor WalkingArrow_cat (Path_cat G))]
  (eta : τ (@Transf WalkingArrow_cat (Path_cat G) F H))
  : τ (@=
      (@Function_grpd Interval_grpd G)
      (walking_interval_extend_object_function G F)
      (walking_interval_extend_object_function G H))
≔ @eq_ap
    (Functor WalkingArrow_cat (Path_cat G))
    (@Function_grpd Interval_grpd G)
    (@walking_interval_extend_object_function G)
    F H
    (@walking_interval_representation_path G F H eta);

// Whole categorical-HIT recursor, functorial in the representation.
injective symbol walking_interval_extend_func
  (G : Grpd)
  : τ (Functor
      (Functor_cat WalkingArrow_cat (Path_cat G))
      (Hom_cat Grpd_cat Interval_grpd G));

// Runtime object beta selects the deployed Interval recursor.
rule @fapp0 _ _ (@walking_interval_extend_func $G) $F
  ↪ @walking_interval_extend_object_function $G $F;

// Selected function obtained by extension.
symbol walking_interval_extend_at
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
  : τ (@Function_grpd Interval_grpd G)
≔ @fapp0
    (Functor_cat WalkingArrow_cat (Path_cat G))
    (Hom_cat Grpd_cat Interval_grpd G)
    (@walking_interval_extend_func G)
    F;

// Judgmental point-constructor observations inherited from interval_rec.
symbol walking_interval_extend_beta_i0
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
  : τ (@= G
      (@walking_interval_extend_at G F interval_i0)
      (@fapp0
        WalkingArrow_cat (Path_cat G) F walking_arrow_src))
≔ @eq_refl
    G
    (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src);

symbol walking_interval_extend_beta_i1
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
  : τ (@= G
      (@walking_interval_extend_at G F interval_i1)
      (@fapp0
        WalkingArrow_cat (Path_cat G) F walking_arrow_tgt))
≔ @eq_refl
    G
    (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt);

// Propositional ordinary-path beta inherited from interval_rec.
symbol walking_interval_extend_beta_generator
  [G : Grpd]
  (F : τ (Functor WalkingArrow_cat (Path_cat G)))
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
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @interval_rec_beta_seg_path
    G
    (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_src)
    (@fapp0 WalkingArrow_cat (Path_cat G) F walking_arrow_tgt)
    (@fapp1_fapp0
      WalkingArrow_cat (Path_cat G) F
      walking_arrow_src walking_arrow_tgt walking_arrow_generator);

// The generic first hom action remains a whole functor.
symbol walking_interval_extend_hom_func
  [G : Grpd]
  [F H : τ (Functor WalkingArrow_cat (Path_cat G))]
  : τ (Functor
      (Hom_cat
        (Functor_cat WalkingArrow_cat (Path_cat G))
        F H)
      (Hom_cat
        (Hom_cat Grpd_cat Interval_grpd G)
        (@walking_interval_extend_at G F)
        (@walking_interval_extend_at G H)))
≔ @fapp1_func
    (Functor_cat WalkingArrow_cat (Path_cat G))
    (Hom_cat Grpd_cat Interval_grpd G)
    (@walking_interval_extend_func G)
    F H;

// First-arrow computation remains scoped propositional signature data.
constant symbol walking_interval_extend_transf_agrees
  [G : Grpd]
  [F H : τ (Functor WalkingArrow_cat (Path_cat G))]
  (eta : τ (@Transf WalkingArrow_cat (Path_cat G) F H))
  : τ (@=
      (@= (@Function_grpd Interval_grpd G)
        (@walking_interval_extend_at G F)
        (@walking_interval_extend_at G H))
      (@fapp1_fapp0
        (Functor_cat WalkingArrow_cat (Path_cat G))
        (Hom_cat Grpd_cat Interval_grpd G)
        (@walking_interval_extend_func G)
        F H eta)
      (@walking_interval_extend_transf_path G F H eta));

// One retained higher action of the whole extension owner.
symbol walking_interval_extend_next_func
  [G : Grpd]
  [F H : τ (Functor WalkingArrow_cat (Path_cat G))]
  [eta theta : τ (@Transf WalkingArrow_cat (Path_cat G) F H)]
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
          F H theta)))
≔ @fapp1_func
    (Hom_cat
      (Functor_cat WalkingArrow_cat (Path_cat G))
      F H)
    (Hom_cat
      (Hom_cat Grpd_cat Interval_grpd G)
      (@walking_interval_extend_at G F)
      (@walking_interval_extend_at G H))
    (@walking_interval_extend_hom_func G F H)
    eta theta;
