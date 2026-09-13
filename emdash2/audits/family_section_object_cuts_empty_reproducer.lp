/*
  NON-LIBRARY SOUNDNESS DIAGNOSTIC — family/section profile collapse.

  Acceptance reproduces an inherited Empty derivation. It is not a positive
  library feature. This file adds no rule, unifier, primitive witness or axiom.
  Do not import it into the library or register it as a positive example.
  See docs/TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md at Git root.
*/
require open emdash.emdash3_2;

symbol profile_raw_transport_path
  [K : Cat] [E D : τ (Functor K Cat_cat)]
  (FF : τ (@Transf K Cat_cat E D))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  (u : τ (Obj (@fapp0 K Cat_cat E x)))
  : τ (@= (Obj (@fapp0 K Cat_cat D y))
      (fapp0 (@fapp1_fapp0 K Cat_cat D x y p)
        (fapp0 (@tapp0_fapp0 K Cat_cat E D x FF) u))
      (fapp0 (@tapp0_fapp0 K Cat_cat E D y FF)
        (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u)))
≔ eq_refl (fapp0 (@tapp1_fapp0 K Cat_cat E D x y FF p) u);

symbol profile_raw_functor_endpoint_path
  [K A : Cat] (F : τ (Functor K A))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  : τ (@= (Obj A) (@fapp0 K A F x) (@fapp0 K A F y))
≔ @profile_raw_transport_path K
    (Const_catd K Terminal_cat) (Const_catd K A) F x y p Terminal_obj;

symbol profile_raw_empty_unit_path
  : τ (@= (Obj Grpd_cat) Empty_grpd Unit_grpd)
≔ @profile_raw_functor_endpoint_path Grpd_cat Grpd_cat
    (@id_func Grpd_cat) Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt);

symbol profile_raw_cuts_empty_witness : τ Empty_grpd
≔ @ind_eq (Obj Grpd_cat) Empty_grpd Unit_grpd
    profile_raw_empty_unit_path (λ G : τ (Obj Grpd_cat), G) tt;

assert ⊢ profile_raw_cuts_empty_witness : τ Empty_grpd;
