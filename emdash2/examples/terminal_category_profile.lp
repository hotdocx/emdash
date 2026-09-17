/* Closed terminal profile: explicit inverse data and bounded eta comparison. */
require open emdash.emdash3_2_terminal_category_profile;
// catalog-area: Categorical contraction and ordinary terminal adjunctions

assert ⊢ @omega_equiv_along_left_inv Cat_cat (Core_cat Terminal_cat) Terminal_cat
  (Core_incl_func Terminal_cat) terminal_category_groupoidal ≡ terminal_category_core_inverse;
assert ⊢ @omega_equiv_along_right_inv Cat_cat (Core_cat Terminal_cat) Terminal_cat
  (Core_incl_func Terminal_cat) terminal_category_groupoidal ≡ terminal_category_core_inverse;
assert (x : τ Unit_grpd) ⊢
  @fapp0 Terminal_cat (Core_cat Terminal_cat) terminal_category_core_inverse x ≡ Terminal_obj;
assert ⊢ @eq_refl (Functor Terminal_cat Terminal_cat) (@id_func Terminal_cat)
  : τ (@= (Functor Terminal_cat Terminal_cat)
      (@Const_func Terminal_cat Terminal_cat Terminal_obj) (@id_func Terminal_cat));
assertnot ⊢ @Const_func Terminal_cat Terminal_cat Terminal_obj ≡ @id_func Terminal_cat;
assertnot (F : τ (Functor Terminal_cat Terminal_cat)) ⊢
  @eq_refl (Functor Terminal_cat Terminal_cat) F
  : τ (@= (Functor Terminal_cat Terminal_cat) F (@id_func Terminal_cat));
assertnot [C : Cat] (c : τ (Obj C)) ⊢
  @eq_refl (Functor C C) (@id_func C)
  : τ (@= (Functor C C) (@Const_func C C c) (@id_func C));
