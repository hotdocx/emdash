/* Transport a component equivalence using whole naturality in an ordinary target. */
require open emdash.emdash3_2_omega_equiv_right_factor;
require open emdash.emdash3_2_strict_transfor_component_paths;

// Whole naturality and mapped input equivalence transport the actual component witness.
symbol one_cat_natural_equivalence_transport [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor I C)) (eta : τ (@Transf I C F G))
 [x y : τ (Obj I)] (m : τ (Hom I x y)) (M : τ (@OmegaEquivAlong I x y m))
 (E : τ (@OmegaEquivAlong C (@fapp0 I C F x) (@fapp0 I C G x) (@tapp0_fapp0 I C F G x eta)))
 : τ (@OmegaEquivAlong C (@fapp0 I C F y) (@fapp0 I C G y) (@tapp0_fapp0 I C F G y eta))
≔ @omega_equiv_right_factor C (@fapp0 I C F x) (@fapp0 I C F y) (@fapp0 I C G y) (@fapp1_fapp0 I C F x y m)
  (@comp_fapp0 C (@fapp0 I C F x) (@fapp0 I C G x) (@fapp0 I C G y) (@fapp1_fapp0 I C G x y m) (@tapp0_fapp0 I C
  F G x eta)) (@tapp0_fapp0 I C F G y eta)
  (@omega_equiv_along_fapp1_fapp0 I C F x y m M)
  (@omega_equiv_along_comp C (@fapp0 I C F x) (@fapp0 I C G x) (@fapp0 I C G y) (@tapp0_fapp0 I C F G x eta)
  (@fapp1_fapp0 I C G x y m) E (@omega_equiv_along_fapp1_fapp0 I C G x y m M))
  (@eq_sym _ _ _ (@strict_component_naturality_path I C F G eta x y m));
