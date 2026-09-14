/* Internalize an object function from a genuinely groupoidal source.
   The existing core inverse and Path_map provide the whole higher action. */
require open emdash.emdash3_2_eq1_evidence_property;

// The selected inverse of the original core inclusion.
symbol groupoidal_core_retraction [A : Cat] (A0 : τ (@IsGroupoidalCat A))
  : τ (Functor A (Core_cat A))
≔ @omega_equiv_along_left_inv Cat_cat (Core_cat A) A (Core_incl_func A) A0;

// The same inverse is identity on objects up to its existing categorical law.
symbol groupoidal_core_retraction_point [A : Cat] (A0 : τ (@IsGroupoidalCat A))
  (a : τ (Obj A))
  : τ (@= (Obj A) (@fapp0 A (Core_cat A) (@groupoidal_core_retraction A A0) a) a)
≔ @eq_ap (Functor A A) (Obj A)
    (λ F : τ (Functor A A), @fapp0 A A F a)
    (@comp_cat_fapp0 A (Core_cat A) A (Core_incl_func A) (@groupoidal_core_retraction A A0))
    (@id_func A)
    (@omega_equiv_left_as_right_law Cat_cat (Core_cat A) A (Core_incl_func A) A0);

// Object functions are whole functors after reflection to the actual core.
symbol groupoidal_object_map_func [A B : Cat] (A0 : τ (@IsGroupoidalCat A))
  (f : τ (@Function_grpd (Obj A) (Obj B))) : τ (Functor A B)
≔ @comp_cat_fapp0 A (Core_cat A) B
    (@comp_cat_fapp0 (Core_cat A) (Core_cat B) B
      (Core_incl_func B) (@path_map_func (Obj A) (Obj B) f))
    (@groupoidal_core_retraction A A0);

// The original object function is recovered propositionally.
symbol groupoidal_object_map_point [A B : Cat] (A0 : τ (@IsGroupoidalCat A))
  (f : τ (@Function_grpd (Obj A) (Obj B))) (a : τ (Obj A))
  : τ (@= (Obj B) (@fapp0 A B (@groupoidal_object_map_func A B A0 f) a) (f a))
≔ @eq_ap (Obj A) (Obj B) f
    (@fapp0 A (Core_cat A) (@groupoidal_core_retraction A A0) a) a
    (@groupoidal_core_retraction_point A A0 a);
