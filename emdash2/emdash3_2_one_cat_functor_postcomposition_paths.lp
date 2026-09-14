require open emdash.emdash3_2;

// Whole native postcomposition observed by a functor with ordinary target.
// The generic strict cut is staged before opposite source normalization.
symbol one_cat_functor_postcomp_path [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B))
  (x y z : τ (Obj A)) (f : τ (Hom A y z)) (g : τ (Hom A x y))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
      (@fapp1_fapp0 A B F x z (@hom_postcomp_fapp0 A A (@id_func A) x y z f g))
      (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp0 A B F z)
        (@fapp1_fapp0 A B F y z f) (@fapp1_fapp0 A B F x y g)))
≔ @eq_trans (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
    (@fapp1_fapp0 A B F x z (@hom_postcomp_fapp0 A A (@id_func A) x y z f g))
    (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z f g))
    (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp0 A B F z)
      (@fapp1_fapp0 A B F y z f) (@fapp1_fapp0 A B F x y g))
    (@eq_ap (Hom A x z) (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
      (@fapp1_fapp0 A B F x z)
      (@hom_postcomp_fapp0 A A (@id_func A) x y z f g) (@comp_fapp0 A x y z f g)
      (@eq_refl (Hom A x z) (@hom_postcomp_fapp0 A A (@id_func A) x y z f g)))
    (@fapp1_comp_path A B F x y z f g);
