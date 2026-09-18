require open emdash.emdash3_2_represented_comma_families;
// catalog-area: Native comma family classification

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (x : τ (Obj K)) ⊢
  @fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x
  ≡ @represented_comma_obj X Y J (@fapp0 K X A x) (@fapp0 K Y D x)
      (@tapp0_fapp0 K Y (@comp_cat_fapp0 K X Y J A) D x h);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  (x y : τ (Obj K)) (g : τ (Hom K x y)) ⊢
  @fapp1_fapp0 (@RepresentedComma_cat X Y J) X (@represented_comma_source_func X Y J) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) y)
    (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x y g)
  ≡ @fapp1_fapp0 K X A x y g;

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  (x y : τ (Obj K)) (g : τ (Hom K x y)) ⊢
  @fapp1_fapp0 (@RepresentedComma_cat X Y J) Y (@represented_comma_target_func X Y J) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x) (@fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) y)
    (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x y g)
  ≡ @fapp1_fapp0 K Y D x y g;

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf K Y
  (@comp_cat_fapp0 K X Y J A) D)) (x : τ (Obj K)) ⊢ @tapp0_fapp0 K X (@represented_comma_family_source_func K X Y J A D h) A x
  (@iso_evidence_to _ _ _ (@represented_comma_family_source_evidence K X Y J A D h)) ≡ @id X (@fapp0 K X A x);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf K Y
  (@comp_cat_fapp0 K X Y J A) D)) (x : τ (Obj K)) ⊢
 @tapp0_fapp0 K X A (@represented_comma_family_source_func K X Y J A D h) x (@iso_evidence_from (Functor_cat K X)
   (@represented_comma_family_source_func K X Y J A D h) A (@represented_comma_family_source_evidence K X Y J A D h))
 ≡ @id X (@fapp0 K X A x);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf K Y
  (@comp_cat_fapp0 K X Y J A) D)) ⊢ @iso_evidence_left (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D h)
  A (@represented_comma_family_source_evidence K X Y J A D h)
 : τ (@= (Hom (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D h) (@represented_comma_family_source_func K X Y J A D h))
     (@comp_fapp0 (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D h) A (@represented_comma_family_source_func K X Y J A D
       h) (@iso_evidence_from (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D h) A
       (@represented_comma_family_source_evidence K X Y J A D h)) (@iso_evidence_to (Functor_cat K X) (@represented_comma_family_source_func
       K X Y J A D h) A (@represented_comma_family_source_evidence K X Y J A D h)))
     (@id (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D h)));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf K Y
  (@comp_cat_fapp0 K X Y J A) D)) ⊢ @iso_evidence_right (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D
  h) A (@represented_comma_family_source_evidence K X Y J A D h)
 : τ (@= (Hom (Functor_cat K X) A A)
     (@comp_fapp0 (Functor_cat K X) A (@represented_comma_family_source_func K X Y J A D h) A (@iso_evidence_to (Functor_cat K
       X) (@represented_comma_family_source_func K X Y J A D h) A (@represented_comma_family_source_evidence K X Y J A D h))
       (@iso_evidence_from (Functor_cat K X) (@represented_comma_family_source_func K X Y J A D h) A
       (@represented_comma_family_source_evidence K X Y J A D h)))
     (@id (Functor_cat K X) A));

assertnot [K : Cat] (F : τ (Functor K K)) ⊢
 @eq_refl (Functor K K) F
 : τ (@= (Functor K K) F (@id_func K));

assertnot [K : Cat] (E : τ (Catd K)) (F : τ (Functor K (@Sigma_cat K E))) ⊢
 @eq_refl (Functor (Op_cat K) (Op_cat K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat (@Sigma_cat K E)) (Op_cat K)
     (@Op_func (@Sigma_cat K E) K (@Sigma_proj1_func K E))
     (@Op_func K (@Sigma_cat K E) F))
 : τ (@= (Functor (Op_cat K) (Op_cat K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat (@Sigma_cat K E)) (Op_cat K)
     (@Op_func (@Sigma_cat K E) K (@Sigma_proj1_func K E))
     (@Op_func K (@Sigma_cat K E) F)) (@id_func (Op_cat K)));

assertnot [B C : Cat] (F G H : τ (Functor B C))
 (f f0 : τ (@Transf B C F G)) (g g0 : τ (@Transf B C G H)) ⊢
 @eq_refl (@Transf B C F H) (@comp_fapp0 (Functor_cat B C) F G H g f)
 : τ (@= (@Transf B C F H) (@comp_fapp0 (Functor_cat B C) F G H g f)
     (@comp_fapp0 (Functor_cat B C) F G H g0 f0));

assertnot [K A : Cat] (F : τ (Functor K (Product_cat K A))) (G : τ (Functor K A)) ⊢
 @eq_refl (Functor K A) (@comp_cat_fapp0 K (Product_cat K A) A (@Product_projR_func K A) F)
 : τ (@= (Functor K A) (@comp_cat_fapp0 K (Product_cat K A) A (@Product_projR_func K A) F) G);

assert [A K : Cat] (F : τ (Functor A K)) (E D : τ (Catd K))
 (FF : τ (@Functord K E D)) (a : τ (Obj A))
 (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 @fapp0 _ _ (@tapp1_fapp0 (@Catd_cat K) Cat_cat
   (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
   (@Sigma_func K) E D (@sigma_pullback_total_transf A K F) FF) (Struct_sigma a u)
 ≡ @Struct_sigma (Obj K) (λ k : τ (Obj K), Obj (@Fibre_cat K D k))
     (@fapp0 A K F a) (@fapp0 _ _ (@Fibre_func K E D FF (@fapp0 A K F a)) u);

assert [A K : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 (a : τ (Obj A)) (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 @fapp0 _ _ (@tapp1_fapp0 (@Catd_cat K) Cat_cat
   (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
   (@Sigma_func K) E E (@sigma_pullback_total_transf A K F) (@id_funcd K E)) (Struct_sigma a u)
 ≡ @Struct_sigma (Obj K) (λ k : τ (Obj K), Obj (@Fibre_cat K E k)) (@fapp0 A K F a) u;

assertnot [A B C : Cat] (F G : τ (Functor B C)) (H : τ (Functor A B)) ⊢
 @eq_refl (Functor A C) (@comp_cat_fapp0 A B C F H)
 : τ (@= (Functor A C) (@comp_cat_fapp0 A B C F H) (@comp_cat_fapp0 A B C G H));

assert [A K C : Cat] (F : τ (Functor A K)) ⊢
 @eq_refl (Functor (Product_cat A C) C)
   (@comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C)
     (@sigma_pullback_total_func A K F (@Const_catd K C)))
 : τ (@= (Functor (Product_cat A C) C)
   (@comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C)
     (@sigma_pullback_total_func A K F (@Const_catd K C))) (@Product_projR_func A C));

assertnot [A K C : Cat] (F : τ (Functor A K)) ⊢
 @comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C)
   (@sigma_pullback_total_func A K F (@Const_catd K C))
 ≡ @Product_projR_func A C;

assertnot [A K C : Cat] (H : τ (Functor (Product_cat A C) (Product_cat K C))) ⊢
 @eq_refl (Functor (Product_cat A C) C)
   (@comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C) H)
 : τ (@= (Functor (Product_cat A C) C)
   (@comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C) H)
   (@Product_projR_func A C));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y)) (x : τ (Obj K)) ⊢
 @tapp0_fapp0 K Y (@represented_comma_family_target_func K X Y J A D h) D x (@one_cat_represented_comma_family_target_to K X Y J A D
  h Y1) ≡ @id Y (@fapp0 K Y D x);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y)) (x : τ (Obj K)) ⊢
 @tapp0_fapp0 K Y D (@represented_comma_family_target_func K X Y J A D h) x (@omega_equiv_along_left_inv (Functor_cat K
  Y) (@represented_comma_family_target_func K X Y J A D h) D (@one_cat_represented_comma_family_target_to K X Y J A D h Y1)
  (@one_cat_represented_comma_family_target_equiv K X Y J A D h Y1)) ≡ @id Y (@fapp0 K Y D x);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y)) ⊢
 @omega_equiv_along_left_law (Functor_cat K Y) (@represented_comma_family_target_func K X Y J A D h) D
  (@one_cat_represented_comma_family_target_to K X Y J A D h Y1) (@one_cat_represented_comma_family_target_equiv K X Y J A D h Y1)
 : τ (@= (Hom (Functor_cat K Y) (@represented_comma_family_target_func K X Y J A D h) (@represented_comma_family_target_func K X Y J A
  D h))
     (@comp_fapp0 (Functor_cat K Y) (@represented_comma_family_target_func K X Y J A D h) D (@represented_comma_family_target_func K X
  Y J A D h) (@omega_equiv_along_left_inv (Functor_cat K Y) (@represented_comma_family_target_func K X Y J A D h) D
  (@one_cat_represented_comma_family_target_to K X Y J A D h Y1) (@one_cat_represented_comma_family_target_equiv K X Y J A D h Y1))
  (@one_cat_represented_comma_family_target_to K X Y J A D h Y1)) (@id (Functor_cat K Y) (@represented_comma_family_target_func K X
  Y J A D h)));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y)) (x : τ (Obj K)) ⊢
 @tapp0_fapp0 K Y D (@represented_comma_family_target_func K X Y J A D h) x (@omega_equiv_along_right_inv (Functor_cat K
  Y) (@represented_comma_family_target_func K X Y J A D h) D (@one_cat_represented_comma_family_target_to K X Y J A D h Y1)
  (@one_cat_represented_comma_family_target_equiv K X Y J A D h Y1)) ≡ @id Y (@fapp0 K Y D x);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X))
 (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (Y1 : τ (IsNCat (cat_succ
  cat_zero) Y)) ⊢
 @omega_equiv_along_right_law (Functor_cat K Y) (@represented_comma_family_target_func K X Y J A D h) D
  (@one_cat_represented_comma_family_target_to K X Y J A D h Y1) (@one_cat_represented_comma_family_target_equiv K X Y J A D h Y1)
 : τ (@= (Hom (Functor_cat K Y) D D)
     (@comp_fapp0 (Functor_cat K Y) D (@represented_comma_family_target_func K X Y J A D h) D
  (@one_cat_represented_comma_family_target_to K X Y J A D h Y1) (@omega_equiv_along_right_inv (Functor_cat K Y)
  (@represented_comma_family_target_func K X Y J A D h) D (@one_cat_represented_comma_family_target_to K X Y J A D h Y1)
  (@one_cat_represented_comma_family_target_equiv K X Y J A D h Y1))) (@id (Functor_cat K Y) D));


symbol ua4_comma_triangle [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y)) (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) (x y : τ (Obj K)) (g : τ (Hom K x y))
 : τ (Obj (@homdc_fibre X Y (@represented_comma_prof X Y J) (@fapp0 K X A x) (@fapp0 K X A y) (@fapp0 K Y D x) (@fapp0 K Y D y) (@tapp0_fapp0 K Y (@comp_cat_fapp0 K X Y J A) D x h) (@tapp0_fapp0 K Y (@comp_cat_fapp0 K X Y J A) D y h) (@fapp1_fapp0 K X A x y g) (sigma_Fst (sigma_Snd (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x y g)))))
≔ sigma_Snd (sigma_Snd (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_family_func K X Y J A D h) x y g));


/* The source next-action conversion passes with the UA-4b recursive Sigma owners. */
symbol ua4_gamma [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D)) : τ (Functor K (@RepresentedComma_cat X Y J))
≔ @represented_comma_family_func K X Y J A D h;


symbol ua4_next_source [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  (x y : τ (Obj K)) (p q : τ (Hom K x y))
  (theta : τ (Hom (Hom_cat K x y) p q))  : τ (Hom (Hom_cat X (@fapp0 K X A x) (@fapp0 K X A y)) (@fapp1_fapp0 K X A x y p) (@fapp1_fapp0 K X A x y q))
≔ @fapp1_fapp0 (Hom_cat (@RepresentedComma_cat X Y J) (@fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) x) (@fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) y)) (Hom_cat X (@fapp0 K X A x) (@fapp0 K X A y)) (@fapp1_func (@RepresentedComma_cat X Y J) X (@represented_comma_source_func X Y J) (@fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) x) (@fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) y)) (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) x y p) (@fapp1_fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) x y q) (@fapp1_fapp0 (Hom_cat K x y) (Hom_cat (@RepresentedComma_cat X Y J) (@fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) x) (@fapp0 K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) y)) (@fapp1_func K (@RepresentedComma_cat X Y J) (@ua4_gamma K X Y J A D h) x y) p q theta);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
  (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
  (x y : τ (Obj K)) (p q : τ (Hom K x y))
  (theta : τ (Hom (Hom_cat K x y) p q))  ⊢
 @ua4_next_source K X Y J A D h x y p q theta
 ≡ @fapp1_fapp0 (Hom_cat K x y) (Hom_cat X (@fapp0 K X A x) (@fapp0 K X A y)) (@fapp1_func K X A x y) p q theta;


/* Append after next_source.lpfragment; arbitrary third cells retain A action. */
assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (h : τ (@Transf K Y (@comp_cat_fapp0 K X Y J A) D))
 (x y : τ (Obj K)) (p q : τ (Hom K x y))
 (theta eta : τ (Hom (Hom_cat K x y) p q))
 (xi : τ (Hom (Hom_cat (Hom_cat K x y) p q) theta eta)) ⊢
@fapp1_fapp0 (Hom_cat (Hom_cat K x y) p q) (Hom_cat (Hom_cat X (@fapp0 K X A x) (@fapp0 K X A y)) (@fapp1_fapp0 K X A x y p) (@fapp1_fapp0 K X A x y q)) (@fapp1_func (Hom_cat K x y) (Hom_cat X (@fapp0 K X A x) (@fapp0 K X A y)) (@fapp1_func K X (@comp_cat_fapp0 K (@RepresentedComma_cat X Y J) X (@represented_comma_source_func X Y J) (@ua4_gamma K X Y J A D h)) x y) p q) theta eta xi
 ≡ @fapp1_fapp0 (Hom_cat (Hom_cat K x y) p q) (Hom_cat (Hom_cat X (@fapp0 K X A x) (@fapp0 K X A y)) (@fapp1_fapp0 K X A x y p) (@fapp1_fapp0 K X A x y q)) (@fapp1_func (Hom_cat K x y) (Hom_cat X (@fapp0 K X A x) (@fapp0 K X A y)) (@fapp1_func K X A x y) p q) theta eta xi;

// Whole internal-Hom input: it need not be presented as the action of h.

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (theta : τ (@Transf (Op_cat K) (@Catd_cat K)
   (@hom_int K K (@id_func K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
     (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (x : τ (Obj K)) ⊢
 @fapp0 K (@RepresentedComma_cat X Y J) (@represented_comma_hom_action_func K X Y J A D theta) x
 ≡ @represented_comma_obj X Y J (@fapp0 K X A x) (@fapp0 K Y D x) (@fapp0 (Hom_cat K x x) (Hom_cat Y (@fapp0 X Y J (@fapp0 K X A x)) (@fapp0 K Y D x))
 (@tapp0_fapp0 K Cat_cat (@hom_ K K (@id_func K) x)
   (@hom_ Y K D (@fapp0 X Y J (@fapp0 K X A x))) x
   (@tapp0_fapp0 (Op_cat K) (@Catd_cat K) (@hom_int K K (@id_func K))
     (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
       (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))) x theta)) (@id K x));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (theta : τ (@Transf (Op_cat K) (@Catd_cat K)
   (@hom_int K K (@id_func K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
     (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (x : τ (Obj K)) ⊢
 @tapp0_fapp0 K X (@represented_comma_hom_action_source_func K X Y J A D theta) A x (@iso_evidence_to (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta))
 ≡ @id X (@fapp0 K X A x);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (theta : τ (@Transf (Op_cat K) (@Catd_cat K)
   (@hom_int K K (@id_func K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
     (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (x : τ (Obj K)) ⊢
 @tapp0_fapp0 K X A (@represented_comma_hom_action_source_func K X Y J A D theta) x (@iso_evidence_from (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta))
 ≡ @id X (@fapp0 K X A x);

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (theta : τ (@Transf (Op_cat K) (@Catd_cat K)
   (@hom_int K K (@id_func K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
     (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) ⊢ @iso_evidence_left (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta)
 : τ (@= (@Transf K X (@represented_comma_hom_action_source_func K X Y J A D theta) (@represented_comma_hom_action_source_func K X Y J A D theta))
 (@comp_fapp0 (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_func K X Y J A D theta) (@iso_evidence_from (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta)) (@iso_evidence_to (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta))) (@id (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta)));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (theta : τ (@Transf (Op_cat K) (@Catd_cat K)
   (@hom_int K K (@id_func K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
     (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) ⊢ @iso_evidence_right (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta)
 : τ (@= (@Transf K X A A)
 (@comp_fapp0 (Functor_cat K X) A (@represented_comma_hom_action_source_func K X Y J A D theta) A (@iso_evidence_to (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta)) (@iso_evidence_from (Functor_cat K X) (@represented_comma_hom_action_source_func K X Y J A D theta) A (@represented_comma_hom_action_source_evidence K X Y J A D theta))) (@id (Functor_cat K X) A));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (theta : τ (@Transf (Op_cat K) (@Catd_cat K)
   (@hom_int K K (@id_func K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
     (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (Y1 : τ (IsNCat (cat_succ cat_zero) Y)) ⊢ (@one_cat_represented_comma_hom_action_target_equiv K X Y J A D theta Y1)
 : τ (@OmegaEquivAlong (Functor_cat K Y) (@represented_comma_hom_action_target_func K X Y J A D theta) D (@one_cat_represented_comma_hom_action_target_to K X Y J A D theta Y1));

assert [K X Y : Cat] (J : τ (Functor X Y)) (A : τ (Functor K X)) (D : τ (Functor K Y))
 (theta : τ (@Transf (Op_cat K) (@Catd_cat K)
   (@hom_int K K (@id_func K))
   (@comp_cat_fapp0 (Op_cat K) (Op_cat Y) (@Catd_cat K)
     (@hom_int Y K D) (@Op_func K Y (@comp_cat_fapp0 K X Y J A))))) (Y1 : τ (IsNCat (cat_succ cat_zero) Y)) (x : τ (Obj K)) ⊢
 @tapp0_fapp0 K Y (@represented_comma_hom_action_target_func K X Y J A D theta) D x (@one_cat_represented_comma_hom_action_target_to K X Y J A D theta Y1) ≡ @id Y (@fapp0 K Y D x);
