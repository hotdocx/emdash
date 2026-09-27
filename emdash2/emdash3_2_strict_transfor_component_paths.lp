/* General component naturality now requires the whole strict-action profile. */
require open emdash.emdash3_2_profile_action_paths;

symbol strict_component_naturality_path
  [I C : Cat] [F G : τ (Functor I C)] (eta : τ (Transf F G))
  (PE : τ (@IsStrictTransfor I C F G eta))
  [x y : τ (Obj I)] (p : τ (Hom I x y))
  : τ (@= (Hom C (@fapp0 I C F x) (@fapp0 I C G y))
      (@comp_fapp0 C _ _ _ (@fapp1_fapp0 I C G x y p) (@tapp0_fapp0 I C F G x eta))
      (@comp_fapp0 C _ _ _ (@tapp0_fapp0 I C F G y eta) (@fapp1_fapp0 I C F x y p)))
≔ @profile_component_naturality_path I C F G eta PE x y p;
