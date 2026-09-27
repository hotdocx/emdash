/* Ordinary naturality of stable evaluated inverse data.
   All paths derive from the original whole DefIso and existing agreements. */
require open emdash.emdash3_2_defiso_evaluation_points;
require open emdash.emdash3_2_one_cat_action_paths;

symbol defiso_at_to_component_path [A B : Cat]
  [F G : τ (Functor A B)] (I : τ (@DefIso (Functor_cat A B) F G))
  (x : τ (Obj A))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G x))
      (@defiso_at_to A B F G I x)
      (@tapp0_fapp0 A B F G x (@defiso_to (Functor_cat A B) F G I)))
≔ @eq_refl (Hom B (@fapp0 A B F x) (@fapp0 A B G x))
    (@defiso_at_to A B F G I x);

symbol defiso_at_to_naturality_path [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (I : τ (@DefIso (Functor_cat A B) F G))
  [x y : τ (Obj A)] (f : τ (Hom A x y))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
      (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B G x) (@fapp0 A B G y)
        (@fapp1_fapp0 A B G x y f) (@defiso_at_to A B F G I x))
      (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp0 A B G y)
        (@defiso_at_to A B F G I y) (@fapp1_fapp0 A B F x y f)))
≔ @eq_trans _ _ _ _
    (@eq_ap (Hom B (@fapp0 A B F x) (@fapp0 A B G x))
      (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
      (λ h : τ (Hom B (@fapp0 A B F x) (@fapp0 A B G x)),
        @comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B G x) (@fapp0 A B G y)
          (@fapp1_fapp0 A B G x y f) h)
      _ _ (@defiso_at_to_component_path A B F G I x))
    (@eq_trans _ _ _ _
      (@one_cat_component_naturality_path A B B1 F G
        (@defiso_to (Functor_cat A B) F G I) x y f)
      (@eq_sym _ _ _
        (@eq_ap (Hom B (@fapp0 A B F y) (@fapp0 A B G y))
          (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
          (λ h : τ (Hom B (@fapp0 A B F y) (@fapp0 A B G y)),
            @comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp0 A B G y)
              h (@fapp1_fapp0 A B F x y f))
          _ _ (@defiso_at_to_component_path A B F G I y))));
