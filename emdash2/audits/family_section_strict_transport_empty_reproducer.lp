/*
  NON-LIBRARY SOUNDNESS DIAGNOSTIC — family/section profile collapse.

  Acceptance reproduces an inherited Empty derivation. It is not a positive
  library feature. This file adds no rule, unifier, primitive witness or axiom.
  Do not import it into the library or register it as a positive example.
  See docs/TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md at Git root.
*/
require open emdash.emdash3_2;

// The current unrestricted family naturality path identifies every pair
// of endpoint values of an ordinary functor along any base arrow.
symbol profile_functor_endpoint_path
  [K A : Cat] (F : τ (Functor K A))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  : τ (@= (Obj A) (@fapp0 K A F x) (@fapp0 K A F y))
≔ @eq_ap
    (Functor Terminal_cat A) (Obj A)
    (λ Q : τ (Functor Terminal_cat A),
      @fapp0 Terminal_cat A Q Terminal_obj)
    (@functord_transport_lhs_func K
      (Const_catd K Terminal_cat) (Const_catd K A) F x y p)
    (@functord_transport_rhs_func K
      (Const_catd K Terminal_cat) (Const_catd K A) F x y p)
    (@functord_transport_strict_naturality K
      (Const_catd K Terminal_cat) (Const_catd K A) F x y p);

symbol profile_empty_unit_path
  : τ (@= (Obj Grpd_cat) Empty_grpd Unit_grpd)
≔ @profile_functor_endpoint_path Grpd_cat Grpd_cat
    (@id_func Grpd_cat) Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt);

symbol profile_constant_section_empty_witness : τ Empty_grpd
≔ @ind_eq (Obj Grpd_cat) Empty_grpd Unit_grpd
    profile_empty_unit_path (λ G : τ (Obj Grpd_cat), G) tt;

assert ⊢ profile_constant_section_empty_witness : τ Empty_grpd;
