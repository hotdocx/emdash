/* Ordinary target paths from the existing ambient laxity cells.
   No rewrite, unifier, new axiom, or caller-provided square is introduced. */
require open emdash.emdash3_2_eq1_hom_action;

// Stage the existing composition/represented-composition comparison
// before applying the arbitrary functor's arrow action.
symbol comp_postcomp_path [A : Cat] [x y z : τ (Obj A)]
  (g : τ (Hom A y z)) (f : τ (Hom A x y))
  : τ (@= (Hom A x z) (@comp_fapp0 A x y z g f)
      (@hom_postcomp_fapp0 A A (@id_func A) x y z g f))
≔ @eq_refl (Hom A x z) (@comp_fapp0 A x y z g f);

symbol one_cat_composition_path [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B))
  [x y z : τ (Obj A)] (g : τ (Hom A y z)) (f : τ (Hom A x y))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
      (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f))
      (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp0 A B F z)
        (@fapp1_fapp0 A B F y z g) (@fapp1_fapp0 A B F x y f)))
≔ @eq_trans _ _ _ _
    (@eq_ap (Hom A x z) (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
      (λ h : τ (Hom A x z), @fapp1_fapp0 A B F x z h)
      (@comp_fapp0 A x y z g f)
      (@hom_postcomp_fapp0 A A (@id_func A) x y z g f)
      (@comp_postcomp_path A x y z g f))
    (@eq_sym _ _ _
      (@hom_to_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F z))
        (B1 (@fapp0 A B F x) (@fapp0 A B F z)) _ _
        (@fapp1_compositor A B F x y z g f)));

symbol one_cat_component_naturality_path [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (epsilon : τ (@Transf A B F G))
  [x y : τ (Obj A)] (f : τ (Hom A x y))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
      (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B G x) (@fapp0 A B G y)
        (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x epsilon))
      (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp0 A B G y)
        (@tapp0_fapp0 A B F G y epsilon) (@fapp1_fapp0 A B F x y f)))
≔ @eq_trans _ _ _ _
    (@hom_to_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (B1 (@fapp0 A B F x) (@fapp0 A B G y)) _ _
      (@tapp1_post_laxity_cell A B F G epsilon x x y f (@id A x)))
    (@eq_sym _ _ _
      (@hom_to_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
        (B1 (@fapp0 A B F x) (@fapp0 A B G y)) _ _
        (@tapp1_pre_laxity_cell A B F G epsilon x y y f (@id A y))));
