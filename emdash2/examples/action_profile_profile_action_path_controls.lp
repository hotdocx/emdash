require open emdash.emdash3_2_profile_action_paths;

assert [A B : Cat] (F : τ (Functor A B)) (PF : τ (@IsStrictFunctor A B F))
 [x y z : τ (Obj A)] (g : τ (Hom A y z)) (f : τ (Hom A x y)) ⊢
 @profile_composition_path A B F PF x y z g f
 : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
   (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f))
   (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B F y z g) (@fapp1_fapp0 A B F x y f)));

assert [A B : Cat] (F G : τ (Functor A B)) (eta : τ (@Transf A B F G))
 (PE : τ (@IsStrictTransfor A B F G eta)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
 @profile_component_naturality_path A B F G eta PE x y f
 : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
   (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x eta))
   (@comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y eta) (@fapp1_fapp0 A B F x y f)));

// Profiles supply paths; they do not install cuts on a raw variable.
assertnot [A B : Cat] (F : τ (Functor A B)) (PF : τ (@IsStrictFunctor A B F))
 [x y z : τ (Obj A)] (g : τ (Hom A y z)) (f : τ (Hom A x y)) ⊢
 @fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f)
 ≡ @comp_fapp0 B _ _ _ (@fapp1_fapp0 A B F y z g) (@fapp1_fapp0 A B F x y f);
assertnot [A B : Cat] (F G : τ (Functor A B)) (eta : τ (@Transf A B F G))
 (PE : τ (@IsStrictTransfor A B F G eta)) [x y : τ (Obj A)] (f : τ (Hom A x y)) ⊢
 @comp_fapp0 B _ _ _ (@fapp1_fapp0 A B G x y f) (@tapp0_fapp0 A B F G x eta)
 ≡ @comp_fapp0 B _ _ _ (@tapp0_fapp0 A B F G y eta) (@fapp1_fapp0 A B F x y f);
