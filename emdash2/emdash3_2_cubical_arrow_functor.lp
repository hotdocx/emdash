/*
  Emdash v3.2: functorial lifting of intrinsic cubical arrows.

  A readable pseudofunctor profile supplies an invertible compositor at the
  post/left and pre/right stable cut presentations. The image of a square
  filler is:

    post_compositor.to ; F_1[alpha] ; pre_compositor.from.

  Thus the lift uses the generic next hom action and standard pseudo
  coherence, not an endpoint rewrite or a cubical-specific map operation.
  Object and visible square actions compute; generic fapp1 retains every
  subsequent hom action.
*/

require open emdash.emdash3_2_cubical_arrow_composition;
require open emdash.emdash3_2_readable_pseudofunctors;
// Raw image of the filler before the two compositor adjustments.
symbol cubical_arrow_map_raw_cell
  [C D : Cat]
  (F : τ (Functor C D))
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  : τ (Hom
      (Hom_cat D (@fapp0 C D F x1) (@fapp0 C D F y2))
      (@fapp1_fapp0 C D F x1 y2
        (@comp_fapp0 C x1 x2 y2 b u))
      (@fapp1_fapp0 C D F x1 y2
        (@comp_fapp0 C x1 y1 y2 v a)))
≔ @fapp1_fapp0
    (Hom_cat C x1 y2)
    (Hom_cat D (@fapp0 C D F x1) (@fapp0 C D F y2))
    (@fapp1_func C D F x1 y2)
    (@comp_fapp0 C x1 x2 y2 b u)
    (@comp_fapp0 C x1 y1 y2 v a)
    alpha;

symbol cubical_arrow_map_cell
  [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  : τ (Obj
      (@homdc_square_fibre
        D
        (@fapp0 C D F x1)
        (@fapp0 C D F y1)
        (@fapp0 C D F x2)
        (@fapp0 C D F y2)
        (@fapp1_fapp0 C D F x1 x2 u)
        (@fapp1_fapp0 C D F y1 y2 v)
        (@fapp1_fapp0 C D F x1 y1 a)
        (@fapp1_fapp0 C D F x2 y2 b)))
≔ @comp_fapp0
    (Hom_cat D (@fapp0 C D F x1) (@fapp0 C D F y2))
    (@hom_postcomp_fapp0
      D D (@id_func D)
      (@fapp0 C D F x1)
      (@fapp0 C D F x2)
      (@fapp0 C D F y2)
      (@fapp1_fapp0 C D F x2 y2 b)
      (@fapp1_fapp0 C D F x1 x2 u))
    (@fapp1_fapp0 C D F x1 y2
      (@comp_fapp0 C x1 y1 y2 v a))
    (@hom_precomp_along_fapp0
      D D (@id_func D)
      (@fapp0 D D (@id_func D) (@fapp0 C D F y2))
      (@fapp0 C D F x1)
      (@fapp0 C D F y1)
      (@fapp1_fapp0 C D F x1 y1 a)
      (@fapp1_fapp0 C D F y1 y2 v))
    (@iso_evidence_from
      (Hom_cat D (@fapp0 C D F x1) (@fapp0 C D F y2))
      (@hom_precomp_along_fapp0
        D D (@id_func D)
        (@fapp0 D D (@id_func D) (@fapp0 C D F y2))
        (@fapp0 C D F x1)
        (@fapp0 C D F y1)
        (@fapp1_fapp0 C D F x1 y1 a)
        (@fapp1_fapp0 C D F y1 y2 v))
      (@fapp1_fapp0 C D F x1 y2
        (@comp_fapp0 C x1 y1 y2 v a))
      (@readable_pseudo_pre_compositor
        C D F P x1 y1 y2 v a))
    (@comp_fapp0
      (Hom_cat D (@fapp0 C D F x1) (@fapp0 C D F y2))
      (@hom_postcomp_fapp0
        D D (@id_func D)
        (@fapp0 C D F x1)
        (@fapp0 C D F x2)
        (@fapp0 C D F y2)
        (@fapp1_fapp0 C D F x2 y2 b)
        (@fapp1_fapp0 C D F x1 x2 u))
      (@fapp1_fapp0 C D F x1 y2
        (@comp_fapp0 C x1 x2 y2 b u))
      (@fapp1_fapp0 C D F x1 y2
        (@comp_fapp0 C x1 y1 y2 v a))
      (@cubical_arrow_map_raw_cell
        C D F x1 y1 x2 y2 u v a b alpha)
      (@iso_evidence_to
        (Hom_cat D (@fapp0 C D F x1) (@fapp0 C D F y2))
        (@hom_postcomp_fapp0
          D D (@id_func D)
          (@fapp0 C D F x1)
          (@fapp0 C D F x2)
          (@fapp0 C D F y2)
          (@fapp1_fapp0 C D F x2 y2 b)
          (@fapp1_fapp0 C D F x1 x2 u))
        (@fapp1_fapp0 C D F x1 y2
          (@comp_fapp0 C x1 x2 y2 b u))
        (@readable_pseudo_post_compositor
          C D F P x1 x2 y2 b u)));

injective symbol CubicalArrow_func
  [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  : τ (Functor (@CubicalArrow_cat C) (@CubicalArrow_cat D));

rule @fapp0 _ _ (@CubicalArrow_func $C $D $F _)
      (Struct_sigma $x (Struct_sigma $y $u))
  ↪ @cubical_edge
      $D
      (@fapp0 $C $D $F $x)
      (@fapp0 $C $D $F $y)
      (@fapp1_fapp0 $C $D $F $x $y $u);

symbol cubical_arrow_map_square
  [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  : τ (Hom
      (@CubicalArrow_cat D)
      (@fapp0
        (@CubicalArrow_cat C) (@CubicalArrow_cat D)
        (@CubicalArrow_func C D F P)
        (@cubical_edge C x1 x2 u))
      (@fapp0
        (@CubicalArrow_cat C) (@CubicalArrow_cat D)
        (@CubicalArrow_func C D F P)
        (@cubical_edge C y1 y2 v)))
≔ @cubical_square
    D
    (@fapp0 C D F x1)
    (@fapp0 C D F y1)
    (@fapp0 C D F x2)
    (@fapp0 C D F y2)
    (@fapp1_fapp0 C D F x1 x2 u)
    (@fapp1_fapp0 C D F y1 y2 v)
    (@fapp1_fapp0 C D F x1 y1 a)
    (@fapp1_fapp0 C D F x2 y2 b)
    (@cubical_arrow_map_cell
      C D F P x1 y1 x2 y2 u v a b alpha);

rule @fapp1_fapp0
      _ _
      (@CubicalArrow_func $C $D $F $P)
      (Struct_sigma $x1 (Struct_sigma $x2 $u))
      (Struct_sigma $y1 (Struct_sigma $y2 $v))
      (Struct_sigma $a (Struct_sigma $b $alpha))
  ↪ @cubical_arrow_map_square
      $C $D $F $P $x1 $y1 $x2 $y2 $u $v $a $b $alpha;

// Source, target, and lifted cubical-arrow functors retain selected readable
// pseudo profiles, enabling recursive face-code lifting.
constant symbol cubical_src_pseudo_profile
  (C : Cat)
  : τ (@ReadablePseudoFunctorProfile
      (@CubicalArrow_cat C) C (@cubical_src_func C));

constant symbol cubical_tgt_pseudo_profile
  (C : Cat)
  : τ (@ReadablePseudoFunctorProfile
      (@CubicalArrow_cat C) C (@cubical_tgt_func C));

constant symbol cubical_arrow_pseudo_profile
  [C D : Cat]
  [F : τ (Functor C D)]
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  : τ (@ReadablePseudoFunctorProfile
      (@CubicalArrow_cat C)
      (@CubicalArrow_cat D)
      (@CubicalArrow_func C D F P));
