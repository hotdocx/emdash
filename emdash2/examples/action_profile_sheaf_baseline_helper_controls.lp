/* Optional source refinement views and retained ordinary helper. */
require open emdash.emdash3_2_commutative_algebra_presheaves;
require open emdash.emdash3_2_one_cat_pointwise_equivalences;

assert [K : Cat] (S : τ (@StrictCommRingPsh K)) ⊢
  @strict_comm_ring_psh K S : τ (@CommRingPsh K);

assert [K : Cat] (S : τ (@StrictCommRingPsh K)) ⊢
  @strict_functor_is_strict (Op_cat K) CommRing_cat S
  : τ (@IsStrictFunctor (Op_cat K) CommRing_cat (@strict_comm_ring_psh K S));

assert [A B : Cat] (B1 : τ (IsNCat (cat_succ cat_zero) B)) [F G : τ (Functor A B)] (eta : τ (@Transf A B F G)) (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta)) (x : τ (Obj A)) ⊢
  @tapp0_fapp0 A B G F x
    (@omega_equiv_along_left_inv (Functor_cat A B) F G eta
      (@one_cat_transf_pointwise_omega_along A B B1 F G eta u))
  ≡ @omega_equiv_along_left_inv B (@fapp0 A B F x) (@fapp0 A B G x)
      (@tapp0_fapp0 A B F G x eta) (u x);

assert [A B : Cat] (B1 : τ (IsNCat (cat_succ cat_zero) B)) [F G : τ (Functor A B)] (eta : τ (@Transf A B F G)) (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta)) (x : τ (Obj A)) ⊢
  @tapp0_fapp0 A B G F x
    (@omega_equiv_along_right_inv (Functor_cat A B) F G eta
      (@one_cat_transf_pointwise_omega_along A B B1 F G eta u))
  ≡ @omega_equiv_along_right_inv B (@fapp0 A B F x) (@fapp0 A B G x)
      (@tapp0_fapp0 A B F G x eta) (u x);
