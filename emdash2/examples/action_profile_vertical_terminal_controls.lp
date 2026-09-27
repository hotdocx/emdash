/* Terminal critical branches have an existing contractibility path.
   This module adds no rewrite or unification rule. */
require open emdash.emdash3_2_gray_profiles;
require open emdash.emdash3_2_nat_arithmetic;

symbol api_terminal_arrow_path
  (u v : τ (Obj Terminal_cat))
  : τ (@= (Obj Terminal_cat) u v)
≔ @is_contr_center (@= Unit_grpd u v) (@unit_is_prop u v);

// Guarded vertical clause 1: its result and the terminal cut.
assert [A : Cat] [F G H : τ (Functor A Terminal_cat)] (epsilon : τ (@Transf A Terminal_cat F G)) (V : τ (@LaxTransfor A Terminal_cat G H)) [X Y Z : τ (Obj A)] (p : τ (Hom A X Y)) (q : τ (Hom A Y Z)) ⊢
  @api_terminal_arrow_path (@tapp1_fapp0 A Terminal_cat F H X Y (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@lax_transfor A Terminal_cat G H V) epsilon) p) Terminal_obj
  : τ (@= (Obj Terminal_cat) (@tapp1_fapp0 A Terminal_cat F H X Y (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@lax_transfor A Terminal_cat G H V) epsilon) p) Terminal_obj);

// Guarded vertical clause 2: its result and the terminal cut.
assert [A : Cat] [F G H : τ (Functor A Terminal_cat)] (epsilon : τ (@Transf A Terminal_cat F G)) (V : τ (@StrictTransfor A Terminal_cat G H)) [X Y Z : τ (Obj A)] (p : τ (Hom A X Y)) (q : τ (Hom A Y Z)) ⊢
  @api_terminal_arrow_path (@tapp1_fapp0 A Terminal_cat F H X Y (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@strict_transfor A Terminal_cat G H V) epsilon) p) Terminal_obj
  : τ (@= (Obj Terminal_cat) (@tapp1_fapp0 A Terminal_cat F H X Y (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@strict_transfor A Terminal_cat G H V) epsilon) p) Terminal_obj);

// Guarded vertical clause 3: its result and the terminal cut.
assert [A : Cat] [F G H : τ (Functor A Terminal_cat)] (U : τ (@StrictTransfor A Terminal_cat F G)) (eta : τ (@Transf A Terminal_cat G H)) [X Y Z : τ (Obj A)] (p : τ (Hom A X Y)) (q : τ (Hom A Y Z)) ⊢
  @api_terminal_arrow_path (@tapp1_fapp0 A Terminal_cat F H X Y (@comp_fapp0 (Functor_cat A Terminal_cat) F G H eta (@strict_transfor A Terminal_cat F G U)) p) Terminal_obj
  : τ (@= (Obj Terminal_cat) (@tapp1_fapp0 A Terminal_cat F H X Y (@comp_fapp0 (Functor_cat A Terminal_cat) F G H eta (@strict_transfor A Terminal_cat F G U)) p) Terminal_obj);

// Guarded vertical clause 4: its result and the terminal cut.
assert [A : Cat] [F G H : τ (Functor A Terminal_cat)] (U : τ (@StrictTransfor A Terminal_cat F G)) (V : τ (@LaxTransfor A Terminal_cat G H)) [X Y Z : τ (Obj A)] (p : τ (Hom A X Y)) (q : τ (Hom A Y Z)) ⊢
  @api_terminal_arrow_path (@tapp1_fapp0 A Terminal_cat F H X Z (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@lax_transfor A Terminal_cat G H V) (@strict_transfor A Terminal_cat F G U)) (@comp_fapp0 A X Y Z q p)) Terminal_obj
  : τ (@= (Obj Terminal_cat) (@tapp1_fapp0 A Terminal_cat F H X Z (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@lax_transfor A Terminal_cat G H V) (@strict_transfor A Terminal_cat F G U)) (@comp_fapp0 A X Y Z q p)) Terminal_obj);

// Guarded vertical clause 5: its result and the terminal cut.
assert [A : Cat] [F G H : τ (Functor A Terminal_cat)] (U : τ (@StrictTransfor A Terminal_cat F G)) (V : τ (@StrictTransfor A Terminal_cat G H)) [X Y Z : τ (Obj A)] (p : τ (Hom A X Y)) (q : τ (Hom A Y Z)) ⊢
  @api_terminal_arrow_path (@tapp1_fapp0 A Terminal_cat F H X Z (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@strict_transfor A Terminal_cat G H V) (@strict_transfor A Terminal_cat F G U)) (@comp_fapp0 A X Y Z q p)) Terminal_obj
  : τ (@= (Obj Terminal_cat) (@tapp1_fapp0 A Terminal_cat F H X Z (@comp_fapp0 (Functor_cat A Terminal_cat) F G H (@strict_transfor A Terminal_cat G H V) (@strict_transfor A Terminal_cat F G U)) (@comp_fapp0 A X Y Z q p)) Terminal_obj);
