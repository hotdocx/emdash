/* Legitimate observations retained by the profile-isolation variants. */
require open emdash.emdash3_2;

symbol profile_section_view
  [K A : Cat] (F : τ (Functor K A))
  : τ (@Transf K Cat_cat (Const_catd K Terminal_cat) (Const_catd K A))
≔ F;

symbol profile_displayed_section_view
  [K A : Cat] (F : τ (Functor K A))
  : τ (@Functord K (Const_catd K Terminal_cat) (Const_catd K A))
≔ F;

assert (K A : Cat) (F : τ (Functor K A)) (x : τ (Obj K))
  ⊢ fapp0
      (@tapp0_fapp0 K Cat_cat
        (Const_catd K Terminal_cat) (Const_catd K A) x F)
      Terminal_obj
    ≡ @fapp0 K A F x;

assert (K A : Cat) (x y : τ (Obj K)) (p : τ (Hom K x y))
  ⊢ @fapp1_fapp0 K Cat_cat (Const_catd K A) x y p
    ≡ @id_func A;

symbol profile_forward_empty_unit : τ (Hom Grpd_cat Empty_grpd Unit_grpd)
≔ λ _ : τ Empty_grpd, tt;

// Ordinary forward action remains available, with its distinct endpoints.
assert ⊢ @fapp1_fapp0 Grpd_cat Grpd_cat (@id_func Grpd_cat)
    Empty_grpd Unit_grpd profile_forward_empty_unit
  ≡ profile_forward_empty_unit;

assert ⊢ @fapp0 Grpd_cat Grpd_cat (@id_func Grpd_cat) Empty_grpd
  ≡ Empty_grpd;
assert ⊢ @fapp0 Grpd_cat Grpd_cat (@id_func Grpd_cat) Unit_grpd
  ≡ Unit_grpd;
assertnot ⊢ Empty_grpd ≡ Unit_grpd;

// An ordinary reflexivity term does not directly cross these endpoints.
// Passing this observation alone is not a consistency result.
assertnot ⊢ @eq_refl (Obj Grpd_cat) Empty_grpd
  : τ (@= (Obj Grpd_cat) Empty_grpd Unit_grpd);
