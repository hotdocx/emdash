/* Ordinary helper through the inherited assembly contract.
   The public OneCat interface and original forward/inverse data are retained. */
require open emdash.emdash3_2_strict_pointwise_equivalences;
require open emdash.emdash3_2_one_cat_transfor_profiles;

symbol one_cat_transf_pointwise_omega_along [A B : Cat]
  (B1 : τ (IsNCat (cat_succ cat_zero) B))
  [F G : τ (Functor A B)] (eta : τ (@Transf A B F G))
  (u : τ (@StrictTransfPointwiseOmegaAlong A B F G eta))
  : τ (@OmegaEquivAlong (Functor_cat A B) F G eta)
≔ @strict_transf_pointwise_omega_along A B F G
    eta u;
