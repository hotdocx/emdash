/* Inherited pointwise assembly accepts raw input and preserves optional strict views and inverse data. */
require open emdash.emdash3_2_gray_profiles;
require open emdash.emdash3_2_strict_pointwise_equivalences;

assert [A B : Cat] [F G : τ (Functor A B)] (S : τ (@StrictTransfor A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G (@strict_transfor_underlying A B F G S))) ⊢
  @strict_transf_pointwise_omega_along A B F G (@strict_transfor_underlying A B F G S) u
  : τ (@OmegaEquivAlong (Functor_cat A B) F G (@strict_transfor_underlying A B F G S));

assert [A B : Cat] [F G : τ (Functor A B)] (S : τ (@StrictTransfor A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G (@strict_transfor_underlying A B F G S))) (x : τ (Obj A)) ⊢
  @tapp0_fapp0 A B G F x (@strict_transf_pointwise_left_inverse A B F G (@strict_transfor_underlying A B F G S) u)
  ≡ @omega_equiv_along_left_inv B (@fapp0 A B F x) (@fapp0 A B G x)
      (@tapp0_fapp0 A B F G x (@strict_transfor_underlying A B F G S)) (u x);

assert [A B : Cat] [F G : τ (Functor A B)] (S : τ (@StrictTransfor A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G (@strict_transfor_underlying A B F G S))) (x : τ (Obj A)) ⊢
  @tapp0_fapp0 A B G F x (@strict_transf_pointwise_right_inverse A B F G (@strict_transfor_underlying A B F G S) u)
  ≡ @omega_equiv_along_right_inv B (@fapp0 A B F x) (@fapp0 A B G x)
      (@tapp0_fapp0 A B F G x (@strict_transfor_underlying A B F G S)) (u x);

assert [A B : Cat] [F G : τ (Functor A B)] (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta)) ⊢
  @strict_transf_pointwise_omega_along A B F G eta u
  : τ (@OmegaEquivAlong (Functor_cat A B) F G eta);
