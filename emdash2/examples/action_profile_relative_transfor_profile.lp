/* UNSELECTED relative profile over complete internal action. Endpoint
   functor laxity is retained through fapp1_at / fapp1_con_at, rather than
   required to be an identity. No inverse assembly or admission is supplied. */
require open emdash.emdash3_2_gray_profiles;

// Existing G action preceded by the actual source component eta[X].
symbol api_transfor_source_component_route
  [A B : Cat] [F G : τ (Functor A B)]
  (eta : τ (@Transf A B F G)) (X : τ (Obj A))
  : τ (@Transf A Cat_cat
    (@hom_ A A (@id_func A) X)
    (@hom_ B A G (@fapp0 A B F X)))
≔ @comp_catd_fapp0 A
    (@hom_ A A (@id_func A) X)
    (@hom_ B A G (@fapp0 A B G X))
    (@hom_ B A G (@fapp0 A B F X))
    (@hom_int_precomp_func B A G (@fapp0 A B G X) (@fapp0 A B F X)
      (@tapp0_fapp0 A B F G X eta))
    (@fapp1_at_transf A B G X);

// Existing F contravariant action followed by the target component eta[Y].
symbol api_transfor_target_component_route
  [A B : Cat] [F G : τ (Functor A B)]
  (eta : τ (@Transf A B F G)) (Y : τ (Obj A))
  : τ (@Transf (Op_cat A) Cat_cat
    (@hom_con A Y A (@id_func A))
    (@hom_con B (@fapp0 A B G Y) A F))
≔ @comp_catd_fapp0 (Op_cat A)
    (@hom_con A Y A (@id_func A))
    (@hom_con B (@fapp0 A B F Y) A F)
    (@hom_con B (@fapp0 A B G Y) A F)
    (@hom_con_int_postcomp_func B A F (@fapp0 A B F Y) (@fapp0 A B G Y)
      (@tapp0_fapp0 A B F G Y eta))
    (@fapp1_con_at_transf A B F Y);

// Each equality concerns a whole internal transfor, not just its components.
symbol api_RelativeTransforProfile
  [A B : Cat] [F G : τ (Functor A B)]
  (eta : τ (@Transf A B F G)) : Grpd
≔ @Product_grpd
    (@Pi_grpd (Obj A) (λ X : τ (Obj A),
      @= (@Transf A Cat_cat
        (@hom_ A A (@id_func A) X)
        (@hom_ B A G (@fapp0 A B F X)))
        (@tapp1_at_transf A B F G X eta)
        (@api_transfor_source_component_route A B F G eta X)))
    (@Pi_grpd (Obj A) (λ Y : τ (Obj A),
      @= (@Transf (Op_cat A) Cat_cat
        (@hom_con A Y A (@id_func A))
        (@hom_con B (@fapp0 A B G Y) A F))
        (@tapp1_con_at_transf A B F G eta Y)
        (@api_transfor_target_component_route A B F G eta Y)));
