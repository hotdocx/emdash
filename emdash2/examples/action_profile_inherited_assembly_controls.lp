/* Inherited contract bookkeeping and ambient noncollapse controls.
   Successful checks do not derive the assumed assembly principle. */
require open emdash.emdash3_2_direct_cover_completion_locality;
require open emdash.emdash3_2_gray_profiles;

assert [A B : Cat] [F G : τ (Functor A B)] (eta : τ (@Transf A B F G)) (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta)) (x : τ (Obj A)) ⊢
  @tapp0_fapp0 A B G F x (@strict_transf_pointwise_left_inverse A B F G eta u)
  ≡ @omega_equiv_along_left_inv B (@fapp0 A B F x) (@fapp0 A B G x)
      (@tapp0_fapp0 A B F G x eta) (u x);

assert [A B : Cat] [F G : τ (Functor A B)] (eta : τ (@Transf A B F G)) (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta)) (x : τ (Obj A)) ⊢
  @tapp0_fapp0 A B G F x (@strict_transf_pointwise_right_inverse A B F G eta u)
  ≡ @omega_equiv_along_right_inv B (@fapp0 A B F x) (@fapp0 A B G x)
      (@tapp0_fapp0 A B F G x eta) (u x);

assert [A B : Cat] [F G : τ (Functor A B)] (eta : τ (@Transf A B F G)) (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta)) ⊢ @strict_transf_pointwise_omega_along A B F G eta u
  : τ (@OmegaEquivAlong (Functor_cat A B) F G eta);

assert [K : Cat] [E D : τ (Catd K)] [FF GG : τ (@Functord K E D)] (eta : τ (@Transfd K E D FF GG)) (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta)) (x : τ (Obj K)) ⊢
  @tdapp0_fapp0 K E D GG FF x (@strict_transfd_pointwise_left_inverse K E D FF GG eta u)
  ≡ @omega_equiv_along_left_inv
      (Functor_cat (@Fibre_cat K E x) (@Fibre_cat K D x))
      (@Fibre_func K E D FF x) (@Fibre_func K E D GG x)
      (@tdapp0_fapp0 K E D FF GG x eta) (u x);

assert [K : Cat] [E D : τ (Catd K)] [FF GG : τ (@Functord K E D)] (eta : τ (@Transfd K E D FF GG)) (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta)) ⊢
  @omega_equiv_along_left_law (@Functord_cat K E D) FF GG eta
    (@strict_transfd_pointwise_omega_along K E D FF GG eta u)
  ≡ @strict_transfd_pointwise_left_law K E D FF GG eta u;

assert [K : Cat] [E D : τ (Catd K)] [FF GG : τ (@Functord K E D)] (eta : τ (@Transfd K E D FF GG)) (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta)) (x : τ (Obj K)) ⊢
  @tdapp0_fapp0 K E D GG FF x (@strict_transfd_pointwise_right_inverse K E D FF GG eta u)
  ≡ @omega_equiv_along_right_inv
      (Functor_cat (@Fibre_cat K E x) (@Fibre_cat K D x))
      (@Fibre_func K E D FF x) (@Fibre_func K E D GG x)
      (@tdapp0_fapp0 K E D FF GG x eta) (u x);

assert [K : Cat] [E D : τ (Catd K)] [FF GG : τ (@Functord K E D)] (eta : τ (@Transfd K E D FF GG)) (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta)) ⊢
  @omega_equiv_along_right_law (@Functord_cat K E D) FF GG eta
    (@strict_transfd_pointwise_omega_along K E D FF GG eta u)
  ≡ @strict_transfd_pointwise_right_law K E D FF GG eta u;

assert [K : Cat] [E D : τ (Catd K)] [FF GG : τ (@Functord K E D)] (eta : τ (@Transfd K E D FF GG)) (u : τ (@StrictTransfdPointwiseOmegaAlong K E D FF GG eta)) ⊢ @strict_transfd_pointwise_omega_along K E D FF GG eta u
  : τ (@OmegaEquivAlong (@Functord_cat K E D) FF GG eta);

// The inherited primitive does not install these generic reflexivity cuts.
assertnot [A B : Cat] (F : τ (Functor A B)) [x y z : τ (Obj A)]
  (f : τ (Hom A x y)) (g : τ (Hom A y z)) ⊢
  @eq_refl (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
    (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
      (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f))
      (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B F y z g) (@fapp1_fapp0 A B F x y f)));

assertnot [A B : Cat] [F G : τ (Functor A B)] (eta : τ (@Transf A B F G))
  [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
  @eq_refl (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
    (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x eta))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
    (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x eta))
    (@comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y eta) (@fapp1_fapp0 A B F x y f)));
