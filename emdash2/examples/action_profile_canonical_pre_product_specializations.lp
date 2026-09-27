require open emdash.emdash3_2;
assert [K C : Cat] (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj K))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) a)))) ⊢
 sigma_Fst (@fapp0 (@Sigma_cat K (@Pullback_catd K K E (@id Cat_cat K))) (Product_cat K C) (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat K) Cat_cat (@Sigma_func K) (@Pullback_catd_func K K (@id Cat_cat K)))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func K K (@id Cat_cat K) (@Const_catd K C))) (@Struct_sigma (Obj K) (λ b : τ (Obj K), Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) b))) a u))
 ≡ @fapp0 K K (@id Cat_cat K) a;

assert [K C : Cat] (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj K))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) a)))) ⊢
 @fapp0 (@Sigma_cat K (@Pullback_catd K K E (@id Cat_cat K))) K (sigma_Fst (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat K) Cat_cat (@Sigma_func K) (@Pullback_catd_func K K (@id Cat_cat K)))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func K K (@id Cat_cat K) (@Const_catd K C)))) (@Struct_sigma (Obj K) (λ b : τ (Obj K), Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) b))) a u)
 ≡ @fapp0 K K (@id Cat_cat K) a;

assert [K C : Cat] (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj K))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) a)))) ⊢
 sigma_Snd (@fapp0 (@Sigma_cat K (@Pullback_catd K K E (@id Cat_cat K))) (Product_cat K C) (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat K) Cat_cat (@Sigma_func K) (@Pullback_catd_func K K (@id Cat_cat K)))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func K K (@id Cat_cat K) (@Const_catd K C))) (@Struct_sigma (Obj K) (λ b : τ (Obj K), Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) b))) a u))
 ≡ @fapp0 (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) a)) C (@Fibre_func K E (@Const_catd K C) FF (@fapp0 K K (@id Cat_cat K) a)) u;

assert [K C : Cat] (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj K))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) a)))) ⊢
 @fapp0 (@Sigma_cat K (@Pullback_catd K K E (@id Cat_cat K))) C (sigma_Snd (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat K) Cat_cat (@Sigma_func K) (@Pullback_catd_func K K (@id Cat_cat K)))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func K K (@id Cat_cat K) (@Const_catd K C)))) (@Struct_sigma (Obj K) (λ b : τ (Obj K), Obj (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) b))) a u)
 ≡ @fapp0 (@Fibre_cat K E (@fapp0 K K (@id Cat_cat K) a)) C (@Fibre_func K E (@Const_catd K C) FF (@fapp0 K K (@id Cat_cat K) a)) u;

assert [A K B C : Cat] (F : τ (Functor A K))
  (FF : τ (@Functord K (@Const_catd K B) (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F a)))) ⊢
 sigma_Fst (@fapp0 (@Sigma_cat A (@Pullback_catd A K (@Const_catd K B) F)) (Product_cat K C) (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) (@Const_catd K B) (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F b))) a u))
 ≡ @fapp0 A K F a;

assert [A K B C : Cat] (F : τ (Functor A K))
  (FF : τ (@Functord K (@Const_catd K B) (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F a)))) ⊢
 @fapp0 (@Sigma_cat A (@Pullback_catd A K (@Const_catd K B) F)) K (sigma_Fst (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) (@Const_catd K B) (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C)))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F b))) a u)
 ≡ @fapp0 A K F a;

assert [A K B C : Cat] (F : τ (Functor A K))
  (FF : τ (@Functord K (@Const_catd K B) (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F a)))) ⊢
 sigma_Snd (@fapp0 (@Sigma_cat A (@Pullback_catd A K (@Const_catd K B) F)) (Product_cat K C) (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) (@Const_catd K B) (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F b))) a u))
 ≡ @fapp0 (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F a)) C (@Fibre_func K (@Const_catd K B) (@Const_catd K C) FF (@fapp0 A K F a)) u;

assert [A K B C : Cat] (F : τ (Functor A K))
  (FF : τ (@Functord K (@Const_catd K B) (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F a)))) ⊢
 @fapp0 (@Sigma_cat A (@Pullback_catd A K (@Const_catd K B) F)) C (sigma_Snd (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) (@Const_catd K B) (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C)))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F b))) a u)
 ≡ @fapp0 (@Fibre_cat K (@Const_catd K B) (@fapp0 A K F a)) C (@Fibre_func K (@Const_catd K B) (@Const_catd K C) FF (@fapp0 A K F a)) u;
