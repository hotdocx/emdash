require open emdash.emdash3_2;

/* Projection laws inherited from the existing generic functor action. */

symbol product_comp_first_path [A B : Cat]
  (x y z : τ (Obj (Product_cat A B)))
  (f : τ (Hom (Product_cat A B) x y)) (g : τ (Hom (Product_cat A B) y z))
  : τ (@= (Hom A (sigma_Fst x) (sigma_Fst z))
      (sigma_Fst (@comp_fapp0 (Product_cat A B) x y z g f))
      (@comp_fapp0 A (sigma_Fst x) (sigma_Fst y) (sigma_Fst z) (sigma_Fst g) (sigma_Fst f)))
≔ @fapp1_comp_path (Product_cat A B) A (@Product_projL_func A B) x y z g f;

symbol product_comp_second_path [A B : Cat]
  (x y z : τ (Obj (Product_cat A B)))
  (f : τ (Hom (Product_cat A B) x y)) (g : τ (Hom (Product_cat A B) y z))
  : τ (@= (Hom B (sigma_Snd x) (sigma_Snd z))
      (sigma_Snd (@comp_fapp0 (Product_cat A B) x y z g f))
      (@comp_fapp0 B (sigma_Snd x) (sigma_Snd y) (sigma_Snd z) (sigma_Snd g) (sigma_Snd f)))
≔ @fapp1_comp_path (Product_cat A B) B (@Product_projR_func A B) x y z g f;
