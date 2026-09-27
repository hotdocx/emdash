/* The source strict-action proof, specialized to the derived ordinary-target
   composition path. The actual raw F, both inverses and laws are retained. */
require open emdash.emdash3_2_one_cat_action_paths;

symbol one_cat_omega_equiv_fmap_left_law
  [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@=
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F x))
      (@comp_fapp0
        B
        (@fapp0 A B F x)
        (@fapp0 A B F y)
        (@fapp0 A B F x)
        (@fapp1_fapp0 A B F y x
          (@omega_equiv_along_left_inv A x y f u))
        (@fapp1_fapp0 A B F x y f))
      (@id B (@fapp0 A B F x)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F x)
      (@fapp0 A B F x))
    (@comp_fapp0
      B
      (@fapp0 A B F x)
      (@fapp0 A B F y)
      (@fapp0 A B F x)
      (@fapp1_fapp0 A B F y x
        (@omega_equiv_along_left_inv A x y f u))
      (@fapp1_fapp0 A B F x y f))
    (@fapp1_fapp0 A B F x x
      (@comp_fapp0 A x y x
        (@omega_equiv_along_left_inv A x y f u)
        f))
    (@id B (@fapp0 A B F x))
    (@eq_sym
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F x))
      (@fapp1_fapp0 A B F x x
        (@comp_fapp0 A x y x
          (@omega_equiv_along_left_inv A x y f u)
          f))
      (@comp_fapp0
        B
        (@fapp0 A B F x)
        (@fapp0 A B F y)
        (@fapp0 A B F x)
        (@fapp1_fapp0 A B F y x
          (@omega_equiv_along_left_inv A x y f u))
        (@fapp1_fapp0 A B F x y f))
      (@one_cat_composition_path
        A B B1 F x y x
        (@omega_equiv_along_left_inv A x y f u)
        f))
    (@eq_ap
      (Hom A x x)
      (Hom B
        (@fapp0 A B F x)
        (@fapp0 A B F x))
      (λ h : τ (Hom A x x),
        @fapp1_fapp0 A B F x x h)
      (@comp_fapp0 A x y x
        (@omega_equiv_along_left_inv A x y f u)
        f)
      (@id A x)
      (@omega_equiv_along_left_law A x y f u));

symbol one_cat_omega_equiv_fmap_right_law
  [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@=
      (Hom B
        (@fapp0 A B F y)
        (@fapp0 A B F y))
      (@comp_fapp0
        B
        (@fapp0 A B F y)
        (@fapp0 A B F x)
        (@fapp0 A B F y)
        (@fapp1_fapp0 A B F x y f)
        (@fapp1_fapp0 A B F y x
          (@omega_equiv_along_right_inv A x y f u)))
      (@id B (@fapp0 A B F y)))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F y)
      (@fapp0 A B F y))
    (@comp_fapp0
      B
      (@fapp0 A B F y)
      (@fapp0 A B F x)
      (@fapp0 A B F y)
      (@fapp1_fapp0 A B F x y f)
      (@fapp1_fapp0 A B F y x
        (@omega_equiv_along_right_inv A x y f u)))
    (@fapp1_fapp0 A B F y y
      (@comp_fapp0 A y x y
        f
        (@omega_equiv_along_right_inv A x y f u)))
    (@id B (@fapp0 A B F y))
    (@eq_sym
      (Hom B
        (@fapp0 A B F y)
        (@fapp0 A B F y))
      (@fapp1_fapp0 A B F y y
        (@comp_fapp0 A y x y
          f
          (@omega_equiv_along_right_inv A x y f u)))
      (@comp_fapp0
        B
        (@fapp0 A B F y)
        (@fapp0 A B F x)
        (@fapp0 A B F y)
        (@fapp1_fapp0 A B F x y f)
        (@fapp1_fapp0 A B F y x
          (@omega_equiv_along_right_inv A x y f u)))
      (@one_cat_composition_path
        A B B1 F y x y f
        (@omega_equiv_along_right_inv A x y f u)))
    (@eq_ap
      (Hom A y y)
      (Hom B
        (@fapp0 A B F y)
        (@fapp0 A B F y))
      (λ h : τ (Hom A y y),
        @fapp1_fapp0 A B F y y h)
      (@comp_fapp0 A y x y
        f
        (@omega_equiv_along_right_inv A x y f u))
      (@id A y)
      (@omega_equiv_along_right_law A x y f u));

symbol one_cat_omega_equiv_fmap
  [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@OmegaEquivAlong
      B
      (@fapp0 A B F x)
      (@fapp0 A B F y)
      (@fapp1_fapp0 A B F x y f))
≔ @omega_equiv_along_intro
    B
    (@fapp0 A B F x)
    (@fapp0 A B F y)
    (@fapp1_fapp0 A B F x y f)
    (@fapp1_fapp0 A B F y x
      (@omega_equiv_along_left_inv A x y f u))
    (@fapp1_fapp0 A B F y x
      (@omega_equiv_along_right_inv A x y f u))
    (@one_cat_omega_equiv_fmap_left_law A B B1 F x y f u)
    (@one_cat_omega_equiv_fmap_right_law A B B1 F x y f u);
