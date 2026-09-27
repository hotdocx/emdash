/* Unit-overlap controls. Base identity orders join at runtime;
   transformation identity orders have independent profile-cell paths. */
require open emdash.examples.action_profile_vertical_identity_paths;

assert [A B : Cat] [F G H : τ (Functor A B)] (epsilon : τ (@Transf A B F G)) (V : τ (@LaxTransfor A B G H)) (X : τ (Obj A)) ⊢ (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H X) (@tapp0_fapp0 A B G H X (@lax_transfor A B G H V)) (@tapp1_fapp0 A B F G X X epsilon (@id A X))) ≡ (@tapp1_fapp0 A B F H X X (@comp_fapp0 (Functor_cat A B) F G H (@lax_transfor A B G H V) epsilon) (@id A X));

assert [A B : Cat] [F G H : τ (Functor A B)] (epsilon : τ (@Transf A B F G)) (V : τ (@StrictTransfor A B G H)) (X : τ (Obj A)) ⊢ (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H X) (@tapp0_fapp0 A B G H X (@strict_transfor A B G H V)) (@tapp1_fapp0 A B F G X X epsilon (@id A X))) ≡ (@tapp1_fapp0 A B F H X X (@comp_fapp0 (Functor_cat A B) F G H (@strict_transfor A B G H V) epsilon) (@id A X));

assert [A B : Cat] [F G H : τ (Functor A B)] (U : τ (@StrictTransfor A B F G)) (eta : τ (@Transf A B G H)) (X : τ (Obj A)) ⊢ (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H X) (@tapp1_fapp0 A B G H X X eta (@id A X)) (@tapp0_fapp0 A B F G X (@strict_transfor A B F G U))) ≡ (@tapp1_fapp0 A B F H X X (@comp_fapp0 (Functor_cat A B) F G H eta (@strict_transfor A B F G U)) (@id A X));

assert [A B : Cat] [F G H : τ (Functor A B)] (U : τ (@StrictTransfor A B F G)) (V : τ (@LaxTransfor A B G H)) (X Z : τ (Obj A)) (q : τ (Hom A X Z)) ⊢ (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H Z) (@tapp1_fapp0 A B G H X Z (@lax_transfor A B G H V) q) (@tapp1_fapp0 A B F G X X (@strict_transfor A B F G U) (@id A X))) ≡ (@tapp1_fapp0 A B F H X Z (@comp_fapp0 (Functor_cat A B) F G H (@lax_transfor A B G H V) (@strict_transfor A B F G U)) (@comp_fapp0 A X X Z q (@id A X)));

assert [A B : Cat] [F G H : τ (Functor A B)] (U : τ (@StrictTransfor A B F G)) (V : τ (@LaxTransfor A B G H)) (X Y : τ (Obj A)) (p : τ (Hom A X Y)) ⊢ (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Y) (@tapp1_fapp0 A B G H Y Y (@lax_transfor A B G H V) (@id A Y)) (@tapp1_fapp0 A B F G X Y (@strict_transfor A B F G U) p)) ≡ (@tapp1_fapp0 A B F H X Y (@comp_fapp0 (Functor_cat A B) F G H (@lax_transfor A B G H V) (@strict_transfor A B F G U)) (@comp_fapp0 A X Y Y (@id A Y) p));

assert [A B : Cat] [F G H : τ (Functor A B)] (U : τ (@StrictTransfor A B F G)) (V : τ (@StrictTransfor A B G H)) (X Z : τ (Obj A)) (q : τ (Hom A X Z)) ⊢ (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G X) (@fapp0 A B H Z) (@tapp1_fapp0 A B G H X Z (@strict_transfor A B G H V) q) (@tapp1_fapp0 A B F G X X (@strict_transfor A B F G U) (@id A X))) ≡ (@tapp1_fapp0 A B F H X Z (@comp_fapp0 (Functor_cat A B) F G H (@strict_transfor A B G H V) (@strict_transfor A B F G U)) (@comp_fapp0 A X X Z q (@id A X)));

assert [A B : Cat] [F G H : τ (Functor A B)] (U : τ (@StrictTransfor A B F G)) (V : τ (@StrictTransfor A B G H)) (X Y : τ (Obj A)) (p : τ (Hom A X Y)) ⊢ (@comp_fapp0 B (@fapp0 A B F X) (@fapp0 A B G Y) (@fapp0 A B H Y) (@tapp1_fapp0 A B G H Y Y (@strict_transfor A B G H V) (@id A Y)) (@tapp1_fapp0 A B F G X Y (@strict_transfor A B F G U) p)) ≡ (@tapp1_fapp0 A B F H X Y (@comp_fapp0 (Functor_cat A B) F G H (@strict_transfor A B G H V) (@strict_transfor A B F G U)) (@comp_fapp0 A X Y Y (@id A Y) p));

assert [A B : Cat] [F G : τ (Functor A B)] (V : τ (@LaxTransfor A B F G)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
  @api_pre_profile_component_to_action A B F G (@lax_transfor A B F G V) (@lax_transfor_is_lax A B F G V) x y f
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
    (@comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y (@lax_transfor A B F G V)) (@fapp1_fapp0 A B F x y f))
    (@tapp1_fapp0 A B F G x y (@lax_transfor A B F G V) f));

assert [A B : Cat] [F G : τ (Functor A B)] (V : τ (@StrictTransfor A B F G)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
  @api_pre_profile_component_to_action A B F G (@strict_transfor A B F G V) (@strict_transfor_pre_evidence A B F G (@strict_transfor A B F G V) (@strict_transfor_is_strict A B F G V)) x y f
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
    (@comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y (@strict_transfor A B F G V)) (@fapp1_fapp0 A B F x y f))
    (@tapp1_fapp0 A B F G x y (@strict_transfor A B F G V) f));

assert [A B : Cat] [F G : τ (Functor A B)] (U : τ (@StrictTransfor A B F G)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
  @api_full_profile_component_to_action A B F G (@strict_transfor A B F G U) (@strict_transfor_is_strict A B F G U) x y f
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
    (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x (@strict_transfor A B F G U)))
    (@tapp1_fapp0 A B F G x y (@strict_transfor A B F G U) f));

// Runtime distinction at the transformation-unit overlaps.
assertnot [A B : Cat] [F G : τ (Functor A B)] (V : τ (@LaxTransfor A B F G)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
  (@comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y (@lax_transfor A B F G V)) (@fapp1_fapp0 A B F x y f))
  ≡ @tapp1_fapp0 A B F G x y (@lax_transfor A B F G V) f;
assertnot [A B : Cat] [F G : τ (Functor A B)] (V : τ (@StrictTransfor A B F G)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
  (@comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y (@strict_transfor A B F G V)) (@fapp1_fapp0 A B F x y f))
  ≡ @tapp1_fapp0 A B F G x y (@strict_transfor A B F G V) f;
assertnot [A B : Cat] [F G : τ (Functor A B)] (U : τ (@StrictTransfor A B F G)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
  (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x (@strict_transfor A B F G U)))
  ≡ @tapp1_fapp0 A B F G x y (@strict_transfor A B F G U) f;
