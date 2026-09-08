/* NON-LIBRARY SOUNDNESS DIAGNOSTIC: Sigma Hom / constant-product conflict.
   This closed empty-type derivation adds only transparent definitions.
   It uses neither the whole op nor pointwise opposite-family constructors.
   Do not import into the library or register as a positive feature test.
   Acceptance reproduces the defect; this is not a repaired kernel. */
require open emdash.emdash3_2;

symbol sigma_hom_source [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) : Cat
≔ Hom_cat (@Sigma_cat K E)
    (@Struct_sigma (Obj K) (λ k : τ (Obj K), Obj (Fibre_cat E k)) x u)
    (@Struct_sigma (Obj K) (λ k : τ (Obj K), Obj (Fibre_cat E k)) y v);

symbol sigma_hom_target [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) : Cat
≔ Op_cat (@Sigma_cat (Op_cat (Hom_cat K x y))
    (@homd_ K E E (@id_funcd K E) x u y v));

symbol sigma_hom_identity_cast [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Functor (@sigma_hom_source K E x y u v)
      (@sigma_hom_target K E x y u v))
≔ @id_func (@sigma_hom_target K E x y u v);

symbol sigma_hom_identity_cast_point [K : Cat] (E : τ (Catd K))
  (x y : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Obj (@sigma_hom_source K E x y u v)))
  : τ (@= (Obj (@sigma_hom_target K E x y u v))
      (@fapp0 (@sigma_hom_source K E x y u v)
        (@sigma_hom_target K E x y u v)
        (@sigma_hom_identity_cast K E x y u v) p) p)
≔ @eq_refl (Obj (@sigma_hom_target K E x y u v)) p;

symbol sigma_constant_hom_cast [C : Cat] (u v : τ (Obj C))
  : τ (Functor (Product_cat Terminal_cat (Hom_cat C u v))
      (Product_cat Terminal_cat (Op_cat (Hom_cat C u v))))
≔ @sigma_hom_identity_cast Terminal_cat (@Const_catd Terminal_cat C)
    Terminal_obj Terminal_obj u v;

symbol sigma_constant_hom_cast_point [C : Cat] (u v : τ (Obj C))
  (p : τ (Obj (Product_cat Terminal_cat (Hom_cat C u v))))
  : τ (@= (Obj (Product_cat Terminal_cat (Op_cat (Hom_cat C u v))))
      (@fapp0 (Product_cat Terminal_cat (Hom_cat C u v))
        (Product_cat Terminal_cat (Op_cat (Hom_cat C u v)))
        (@sigma_constant_hom_cast C u v) p) p)
≔ @sigma_hom_identity_cast_point Terminal_cat (@Const_catd Terminal_cat C)
    Terminal_obj Terminal_obj u v p;

symbol sigma_hom_prod_source [C : Cat] (u v : τ (Obj C)) : Cat
≔ Product_cat Terminal_cat (Hom_cat C u v);
symbol sigma_hom_prod_target [C : Cat] (u v : τ (Obj C)) : Cat
≔ Product_cat Terminal_cat (Op_cat (Hom_cat C u v));

symbol sigma_hom_cast_image [C : Cat] (u v : τ (Obj C))
  (p : τ (Obj (@sigma_hom_prod_source C u v)))
  : τ (Obj (@sigma_hom_prod_target C u v))
≔ @fapp0 (@sigma_hom_prod_source C u v) (@sigma_hom_prod_target C u v)
    (@sigma_constant_hom_cast C u v) p;

symbol sigma_hom_recentered_arrow [C : Cat] (u v : τ (Obj C))
  (p q : τ (Obj (@sigma_hom_prod_source C u v)))
  (a : τ (Hom (@sigma_hom_prod_source C u v) p q))
  : τ (Hom (@sigma_hom_prod_target C u v) p q)
≔ @comp_fapp0 (@sigma_hom_prod_target C u v)
    p (@sigma_hom_cast_image C u v q) q
    (@path_to_hom (@sigma_hom_prod_target C u v)
      (@sigma_hom_cast_image C u v q) q
      (@sigma_constant_hom_cast_point C u v q))
    (@comp_fapp0 (@sigma_hom_prod_target C u v)
      p (@sigma_hom_cast_image C u v p) (@sigma_hom_cast_image C u v q)
      (@fapp1_fapp0 (@sigma_hom_prod_source C u v)
        (@sigma_hom_prod_target C u v) (@sigma_constant_hom_cast C u v) p q a)
      (@path_to_hom (@sigma_hom_prod_target C u v)
        p (@sigma_hom_cast_image C u v p)
        (@eq_sym (Obj (@sigma_hom_prod_target C u v))
          (@sigma_hom_cast_image C u v p) p
          (@sigma_constant_hom_cast_point C u v p))));

symbol sigma_hom_arrow_reverse [C : Cat]
  (x y : τ (Obj C)) (f : τ (Hom C x y)) : τ (Hom C y x)
≔ @tapp0_fapp0 Terminal_cat C
    (@Obj_func C y) (@Obj_func C x) Terminal_obj
    (@sigma_Snd (Obj Terminal_cat)
      (λ _ : τ (Obj Terminal_cat),
        Obj (@Transf_cat Terminal_cat C (@Obj_func C y) (@Obj_func C x)))
      (@sigma_hom_recentered_arrow Cat_cat Terminal_cat C
        (@Product_pair Terminal_cat (Functor_cat Terminal_cat C)
          Terminal_obj (@Obj_func C x))
        (@Product_pair Terminal_cat (Functor_cat Terminal_cat C)
          Terminal_obj (@Obj_func C y))
        (@Product_pair Terminal_cat
          (@Transf_cat Terminal_cat C (@Obj_func C x) (@Obj_func C y))
          Terminal_obj (@Const_transf Terminal_cat C x y f))));

symbol sigma_hom_empty_witness : τ Empty_grpd
≔ (@sigma_hom_arrow_reverse Grpd_cat Empty_grpd Unit_grpd
    (λ _ : τ Empty_grpd, tt)) tt;

assert ⊢ sigma_hom_empty_witness : τ Empty_grpd;
