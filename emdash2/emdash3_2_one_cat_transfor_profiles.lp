/* Whole ordinary-target transfor evidence from the existing two cells. */
require open emdash.emdash3_2_one_cat_functor_profiles;

symbol one_cat_post_strict [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (epsilon : τ (@Transf A B F G))
  : τ (@IsPostStrictTransfor A B F G epsilon)
≔ λ X : τ (Obj A), λ Y : τ (Obj A), λ Z : τ (Obj A),
  λ g : τ (Hom A Y Z),
    @discrete_cell_is_strict
      (Functor_cat (Hom_cat A X Y) (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z)))
      (@discrete_functor_category (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
        (B1 (@fapp0 A B F X) (@fapp0 A B G Z)))
      (@strict_transfor_naturality_lhs_func A B F G epsilon X Y Z g)
      (@strict_transfor_naturality_rhs_func A B F G epsilon X Y Z g)
      (@strict_transfor_naturality_transf A B F G epsilon X Y Z g);

symbol one_cat_pre_strict [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (epsilon : τ (@Transf A B F G))
  : τ (@IsPreStrictTransfor A B F G epsilon)
≔ λ Y : τ (Obj A), λ W : τ (Obj A), λ X : τ (Obj A),
  λ h : τ (Hom A W X),
    @discrete_cell_is_strict
      (Functor_cat (Hom_cat A X Y) (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
      (@discrete_functor_category (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
        (B1 (@fapp0 A B F W) (@fapp0 A B G Y)))
      (@strict_transfor_pre_naturality_lhs_func A B F G epsilon Y W X h)
      (@strict_transfor_pre_naturality_rhs_func A B F G epsilon Y W X h)
      (@strict_transfor_pre_naturality_transf A B F G epsilon Y W X h);

symbol one_cat_transfor_is_strict [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (epsilon : τ (@Transf A B F G))
  : τ (@IsStrictTransfor A B F G epsilon)
≔ @strict_transfor_strictness_intro A B F G epsilon
    (@one_cat_post_strict A B B1 F G epsilon)
    (@one_cat_pre_strict A B B1 F G epsilon);

symbol one_cat_strict_transfor [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (epsilon : τ (@Transf A B F G))
  : τ (@StrictTransfor A B F G)
≔ @make_strict_transfor A B F G epsilon
    (@one_cat_transfor_is_strict A B B1 F G epsilon);

assert [A B : Cat] (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (epsilon : τ (@Transf A B F G)) ⊢
  @strict_transfor_underlying A B F G (@one_cat_strict_transfor A B B1 F G epsilon)
  ≡ epsilon;

// Ordinary target supplies the conventional pre/right admission as well.
symbol one_cat_lax_transfor [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (epsilon : τ (@Transf A B F G))
  : τ (@LaxTransfor A B F G)
≔ @make_lax_transfor A B F G epsilon
    (@one_cat_pre_strict A B B1 F G epsilon);
