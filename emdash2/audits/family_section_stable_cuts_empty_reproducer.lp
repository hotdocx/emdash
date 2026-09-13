/*
  NON-LIBRARY SOUNDNESS DIAGNOSTIC — family/section profile collapse.

  Acceptance reproduces an inherited Empty derivation. It is not a positive
  library feature. This file adds no rule, unifier, primitive witness or axiom.
  Do not import it into the library or register it as a positive example.
  See docs/TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md at Git root.
*/
require open emdash.emdash3_2;

symbol profile_stable_left
  [K : Cat] [E D : τ (Functor K Cat_cat)]
  (FF : τ (@Transf K Cat_cat E D))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  : τ (@= (Functor (fapp0 E x) (fapp0 D y))
      (comp_cat_fapp0 (@fapp1_fapp0 K Cat_cat D x y p)
        (@tapp0_fapp0 K Cat_cat E D x FF))
      (@tapp1_fapp0 K Cat_cat E D x y FF p))
≔ eq_refl (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
    (fapp0 E x) (fapp0 D x) (fapp0 D y)
    (@fapp1_fapp0 K Cat_cat D x y p)
    (@tapp0_fapp0 K Cat_cat E D x FF));

symbol profile_stable_right
  [K : Cat] [E D : τ (Functor K Cat_cat)]
  (FF : τ (@Transf K Cat_cat E D))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  : τ (@= (Functor (fapp0 E x) (fapp0 D y))
      (comp_cat_fapp0 (@tapp0_fapp0 K Cat_cat E D y FF)
        (@fapp1_fapp0 K Cat_cat E x y p))
      (@tapp1_fapp0 K Cat_cat E D x y FF p))
≔ eq_refl (@hom_precomp_along_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
    (fapp0 D y) (fapp0 E x) (fapp0 E y)
    (@fapp1_fapp0 K Cat_cat E x y p)
    (@tapp0_fapp0 K Cat_cat E D y FF));

symbol profile_stable_functor_endpoint_path
  [K A : Cat] (F : τ (Functor K A))
  [x y : τ (Obj K)] (p : τ (Hom K x y))
  : τ (@= (Obj A) (@fapp0 K A F x) (@fapp0 K A F y))
≔ @eq_ap (Functor Terminal_cat A) (Obj A)
    (λ Q : τ (Functor Terminal_cat A), fapp0 Q Terminal_obj)
    (comp_cat_fapp0
      (@fapp1_fapp0 K Cat_cat (Const_catd K A) x y p)
      (@tapp0_fapp0 K Cat_cat
        (Const_catd K Terminal_cat) (Const_catd K A) x F))
    (comp_cat_fapp0
      (@tapp0_fapp0 K Cat_cat
        (Const_catd K Terminal_cat) (Const_catd K A) y F)
      (@fapp1_fapp0 K Cat_cat (Const_catd K Terminal_cat) x y p))
    (eq_trans
      (@profile_stable_left K
        (Const_catd K Terminal_cat) (Const_catd K A) F x y p)
      (eq_sym (@profile_stable_right K
        (Const_catd K Terminal_cat) (Const_catd K A) F x y p)));

symbol profile_stable_empty_unit_path
  : τ (@= (Obj Grpd_cat) Empty_grpd Unit_grpd)
≔ @profile_stable_functor_endpoint_path Grpd_cat Grpd_cat
    (@id_func Grpd_cat) Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt);

symbol profile_stable_cuts_empty_witness : τ Empty_grpd
≔ @ind_eq (Obj Grpd_cat) Empty_grpd Unit_grpd
    profile_stable_empty_unit_path (λ G : τ (Obj Grpd_cat), G) tt;

assert ⊢ profile_stable_cuts_empty_witness : τ Empty_grpd;
