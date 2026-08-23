/*
  Reviewer example: readable pseudo profiles and whole CubicalArrow lifting.
*/

require open emdash.emdash3_2_cubical_arrow_functor;

// The mapped filler has the required composite-side square boundary.
assert [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @cubical_arrow_map_cell C D F P x1 y1 x2 y2 u v a b alpha
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
        (@fapp1_fapp0 C D F x2 y2 b)));

// Edge and square actions compute through the same whole lifted functor.
assert [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  (x y : τ (Obj C))
  (u : τ (Hom C x y)) ⊢
  @fapp0
    (@CubicalArrow_cat C) (@CubicalArrow_cat D)
    (@CubicalArrow_func C D F P)
    (@cubical_edge C x y u)
  ≡ @cubical_edge
      D
      (@fapp0 C D F x)
      (@fapp0 C D F y)
      (@fapp1_fapp0 C D F x y u);

assert [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp1_fapp0
    (@CubicalArrow_cat C) (@CubicalArrow_cat D)
    (@CubicalArrow_func C D F P)
    (@cubical_edge C x1 x2 u)
    (@cubical_edge C y1 y2 v)
    (@cubical_square C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_arrow_map_square
      C D F P x1 y1 x2 y2 u v a b alpha;

// Source/target projection of the mapped square gives the separately mapped
// side arrows, as required for recursive face action.
assert [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp1_fapp0
    (@CubicalArrow_cat D) D
    (@cubical_src_func D)
    (@fapp0
      (@CubicalArrow_cat C) (@CubicalArrow_cat D)
      (@CubicalArrow_func C D F P)
      (@cubical_edge C x1 x2 u))
    (@fapp0
      (@CubicalArrow_cat C) (@CubicalArrow_cat D)
      (@CubicalArrow_func C D F P)
      (@cubical_edge C y1 y2 v))
    (@cubical_arrow_map_square
      C D F P x1 y1 x2 y2 u v a b alpha)
  ≡ @fapp1_fapp0 C D F x1 y1 a;

assert [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp1_fapp0
    (@CubicalArrow_cat D) D
    (@cubical_tgt_func D)
    (@fapp0
      (@CubicalArrow_cat C) (@CubicalArrow_cat D)
      (@CubicalArrow_func C D F P)
      (@cubical_edge C x1 x2 u))
    (@fapp0
      (@CubicalArrow_cat C) (@CubicalArrow_cat D)
      (@CubicalArrow_func C D F P)
      (@cubical_edge C y1 y2 v))
    (@cubical_arrow_map_square
      C D F P x1 y1 x2 y2 u v a b alpha)
  ≡ @fapp1_fapp0 C D F x2 y2 b;

// The lift remains whole and iterable at the next hom.
assert [C D : Cat]
  (F : τ (Functor C D))
  (P : τ (@ReadablePseudoFunctorProfile C D F))
  (U V : τ (Obj (@CubicalArrow_cat C))) ⊢
  @fapp1_func
    (@CubicalArrow_cat C) (@CubicalArrow_cat D)
    (@CubicalArrow_func C D F P) U V
  : τ (Functor
      (Hom_cat (@CubicalArrow_cat C) U V)
      (Hom_cat
        (@CubicalArrow_cat D)
        (@fapp0
          (@CubicalArrow_cat C) (@CubicalArrow_cat D)
          (@CubicalArrow_func C D F P) U)
        (@fapp0
          (@CubicalArrow_cat C) (@CubicalArrow_cat D)
          (@CubicalArrow_func C D F P) V)));

// Profiles required by recursive left/right/star face action are available.
assert [C : Cat] ⊢
  @cubical_src_pseudo_profile C
  : τ (@ReadablePseudoFunctorProfile
      (@CubicalArrow_cat C) C (@cubical_src_func C));

assert [C : Cat] ⊢
  @cubical_tgt_pseudo_profile C
  : τ (@ReadablePseudoFunctorProfile
      (@CubicalArrow_cat C) C (@cubical_tgt_func C));

assert [C D : Cat]
  [F : τ (Functor C D)]
  (P : τ (@ReadablePseudoFunctorProfile C D F)) ⊢
  @cubical_arrow_pseudo_profile C D F P
  : τ (@ReadablePseudoFunctorProfile
      (@CubicalArrow_cat C)
      (@CubicalArrow_cat D)
      (@CubicalArrow_func C D F P));
