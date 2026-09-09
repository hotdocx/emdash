/* First-class component naturality in the current globally strict profile.
   This rule-free proof explicitly crosses the existing raw/post/pre/mixed
   usability owners. It is not a theorem about arbitrary lax transformations;
   a later strictness migration must keep its strict hypothesis explicit. */
require open emdash.emdash3_2;

symbol strict_component_naturality_path
  [I C : Cat] [F G : τ (Functor I C)] (eta : τ (Transf F G))
  [x y : τ (Obj I)] (p : τ (Hom I x y))
  : τ (@= (Hom C (@fapp0 I C F x) (@fapp0 I C G y))
      (@comp_fapp0 C _ _ _ (@fapp1_fapp0 I C G x y p) (@tapp0_fapp0 I C F G x eta))
      (@comp_fapp0 C _ _ _ (@tapp0_fapp0 I C F G y eta) (@fapp1_fapp0 I C F x y p)))
≔ @eq_trans (Hom C (@fapp0 I C F x) (@fapp0 I C G y))
    (@comp_fapp0 C _ _ _ (@fapp1_fapp0 I C G x y p) (@tapp0_fapp0 I C F G x eta))
    (@hom_postcomp_fapp0 C C (@id_func C) _ _ _
      (@fapp1_fapp0 I C G x y p) (@tapp0_fapp0 I C F G x eta))
    (@comp_fapp0 C _ _ _ (@tapp0_fapp0 I C F G y eta) (@fapp1_fapp0 I C F x y p))
    (eq_refl (@comp_fapp0 C _ _ _ (@fapp1_fapp0 I C G x y p) (@tapp0_fapp0 I C F G x eta)))
    (@eq_trans (Hom C (@fapp0 I C F x) (@fapp0 I C G y))
      (@hom_postcomp_fapp0 C C (@id_func C) _ _ _
        (@fapp1_fapp0 I C G x y p) (@tapp0_fapp0 I C F G x eta))
      (@tapp1_fapp0 I C F G x y eta p)
      (@comp_fapp0 C _ _ _ (@tapp0_fapp0 I C F G y eta) (@fapp1_fapp0 I C F x y p))
      (eq_refl (@tapp1_fapp0 I C F G x y eta p))
      (@eq_trans (Hom C (@fapp0 I C F x) (@fapp0 I C G y))
        (@tapp1_fapp0 I C F G x y eta p)
        (@hom_precomp_along_fapp0 C C (@id_func C) _ _ _
          (@fapp1_fapp0 I C F x y p) (@tapp0_fapp0 I C F G y eta))
        (@comp_fapp0 C _ _ _ (@tapp0_fapp0 I C F G y eta) (@fapp1_fapp0 I C F x y p))
        (eq_refl (@tapp1_fapp0 I C F G x y eta p))
        (eq_refl (@hom_precomp_along_fapp0 C C (@id_func C) _ _ _
          (@fapp1_fapp0 I C F x y p) (@tapp0_fapp0 I C F G y eta)))));
