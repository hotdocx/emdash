/* Independent semantic paths for transformation-identity overlaps.
   These use the existing profile cells, not the new vertical-fold rules. */
require open emdash.emdash3_2_gray_profiles;

symbol api_pre_profile_component_to_action
  [A B : Cat] [F G : τ (Functor A B)] (eta : τ (@Transf A B F G))
  (PN : τ (@IsPreStrictTransfor A B F G eta))
  [x y : τ (Obj A)] (f : τ (Hom A x y))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
    (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp0 A B G y)
      (@tapp0_fapp0 A B F G y eta) (@fapp1_fapp0 A B F x y f))
    (@tapp1_fapp0 A B F G x y eta f))
≔ @strict_cell_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@fapp0 (Hom_cat A y y) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@strict_transfor_pre_naturality_lhs_func A B F G eta y x y f) (@id A y))
    (@fapp0 (Hom_cat A y y) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@strict_transfor_pre_naturality_rhs_func A B F G eta y x y f) (@id A y))
    (@tapp1_pre_laxity_cell A B F G eta x y y f (@id A y))
    (@pre_strict_transfor_naturality_evidence A B F G eta PN x y y f (@id A y));

symbol api_full_profile_component_to_action
  [A B : Cat] [F G : τ (Functor A B)] (eta : τ (@Transf A B F G))
  (PE : τ (@IsStrictTransfor A B F G eta))
  [x y : τ (Obj A)] (f : τ (Hom A x y))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
    (@comp_fapp0 B (@fapp0 A B F x) (@fapp0 A B G x) (@fapp0 A B G y)
      (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x eta))
    (@tapp1_fapp0 A B F G x y eta f))
≔ @strict_cell_path (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
    (@fapp0 (Hom_cat A x x) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@strict_transfor_naturality_lhs_func A B F G eta x x y f) (@id A x))
    (@fapp0 (Hom_cat A x x) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@strict_transfor_naturality_rhs_func A B F G eta x x y f) (@id A x))
    (@tapp1_post_laxity_cell A B F G eta x x y f (@id A x))
    (@strict_transfor_naturality_evidence A B F G eta PE x x y f (@id A x));
