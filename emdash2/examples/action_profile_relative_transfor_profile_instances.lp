/* Candidate profile producers. Existing normal units and path induction
   retain arbitrary endpoint functors; no strict-functor evidence is required. */
require open emdash.examples.action_profile_relative_transfor_profile;

// Stage the normal-unit law before a concrete functor's action projects.
symbol api_normal_functor_identity_path
  [A B : Cat] (F : τ (Functor A B)) (x : τ (Obj A))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F x))
    (@fapp1_fapp0 A B F x x (@id A x))
    (@id B (@fapp0 A B F x)))
≔ @eq_refl (Hom B (@fapp0 A B F x) (@fapp0 A B F x))
    (@id B (@fapp0 A B F x));

// Identity specialization of the whole source-component factorization.
symbol api_relative_identity_source_path
  [A B : Cat] (F : τ (Functor A B)) (X : τ (Obj A))
  : τ (@= (@Transf A Cat_cat (@hom_ A A (@id_func A) X) (@hom_ B A F (@fapp0 A B F X))) (@fapp1_at_transf A B F X) (@api_transfor_source_component_route A B F F (@id (Functor_cat A B) F) X))
≔ @eq_sym (@Transf A Cat_cat (@hom_ A A (@id_func A) X) (@hom_ B A F (@fapp0 A B F X))) (@api_transfor_source_component_route A B F F (@id (Functor_cat A B) F) X) (@fapp1_at_transf A B F X)
    (@eq_ap (Hom (@Catd_cat A) (@hom_ B A F (@fapp0 A B F X)) (@hom_ B A F (@fapp0 A B F X))) (@Transf A Cat_cat (@hom_ A A (@id_func A) X) (@hom_ B A F (@fapp0 A B F X)))
      (λ k : τ (Hom (@Catd_cat A) (@hom_ B A F (@fapp0 A B F X)) (@hom_ B A F (@fapp0 A B F X))), @comp_catd_fapp0 A (@hom_ A A (@id_func A) X) (@hom_ B A F (@fapp0 A B F X)) (@hom_ B A F (@fapp0 A B F X)) k (@fapp1_at_transf A B F X))
      (@hom_int_precomp_func B A F (@fapp0 A B F X) (@fapp0 A B F X) (@id B (@fapp0 A B F X))) (@id (@Catd_cat A) (@hom_ B A F (@fapp0 A B F X))) (@api_normal_functor_identity_path (Op_cat B) (@Catd_cat A) (@hom_int B A F) (@fapp0 A B F X)));

// Identity specialization of the whole target-component factorization.
symbol api_relative_identity_target_path
  [A B : Cat] (F : τ (Functor A B)) (Y : τ (Obj A))
  : τ (@= (@Transf (Op_cat A) Cat_cat (@hom_con A Y A (@id_func A)) (@hom_con B (@fapp0 A B F Y) A F)) (@fapp1_con_at_transf A B F Y) (@api_transfor_target_component_route A B F F (@id (Functor_cat A B) F) Y))
≔ @eq_sym (@Transf (Op_cat A) Cat_cat (@hom_con A Y A (@id_func A)) (@hom_con B (@fapp0 A B F Y) A F)) (@api_transfor_target_component_route A B F F (@id (Functor_cat A B) F) Y) (@fapp1_con_at_transf A B F Y)
    (@eq_ap (Hom (@Catd_cat (Op_cat A)) (@hom_con B (@fapp0 A B F Y) A F) (@hom_con B (@fapp0 A B F Y) A F)) (@Transf (Op_cat A) Cat_cat (@hom_con A Y A (@id_func A)) (@hom_con B (@fapp0 A B F Y) A F))
      (λ k : τ (Hom (@Catd_cat (Op_cat A)) (@hom_con B (@fapp0 A B F Y) A F) (@hom_con B (@fapp0 A B F Y) A F)), @comp_catd_fapp0 (Op_cat A) (@hom_con A Y A (@id_func A)) (@hom_con B (@fapp0 A B F Y) A F) (@hom_con B (@fapp0 A B F Y) A F) k (@fapp1_con_at_transf A B F Y))
      (@hom_con_int_postcomp_func B A F (@fapp0 A B F Y) (@fapp0 A B F Y) (@id B (@fapp0 A B F Y))) (@id (@Catd_cat (Op_cat A)) (@hom_con B (@fapp0 A B F Y) A F)) (@api_normal_functor_identity_path B (@Catd_cat (Op_cat A)) (@hom_con_int B A F) (@fapp0 A B F Y)));

// Identity is admitted for every raw endpoint functor, with its own laxity.
symbol api_relative_identity_transfor_profile
  [A B : Cat] (F : τ (Functor A B))
  : τ (@api_RelativeTransforProfile A B F F (@id (Functor_cat A B) F))
≔ Struct_sigma
    (λ X : τ (Obj A), @api_relative_identity_source_path A B F X)
    (λ Y : τ (Obj A), @api_relative_identity_target_path A B F Y);

// A path-induced whole transformation inherits the relative profile by J.
symbol api_relative_path_transfor_profile
  [A B : Cat] [F G : τ (Functor A B)]
  (path : τ (@= (Functor A B) F G))
  : τ (@api_RelativeTransforProfile A B F G
    (@path_to_hom (Functor_cat A B) F G path))
≔ @ind_eqr (Functor A B) G
    (λ H : τ (Functor A B), λ p : τ (@= (Functor A B) H G),
      @api_RelativeTransforProfile A B H G
        (@path_to_hom (Functor_cat A B) H G p))
    (@api_relative_identity_transfor_profile A B G)
    F path;
