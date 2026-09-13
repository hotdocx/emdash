/* NON-LIBRARY: higher action is typed here; its final component formula
   is not yet qualified by this focused dependency slice. */
/* TEST ONLY: observe the existing whole action at a source 2-cell. */
require open emdash.hom_presheaf_transpose_action_controls;

symbol test_hom_presheaf_source_two_cell [Z : Cat]
  (x xp : τ (Obj Z)) (r s : τ (Hom Z x xp))
  (alpha : τ (Hom (Hom_cat Z x xp) r s)) (y : τ (Obj Z))
  (H : τ (Functor (Transpose_cat (Hom_cat Z x y)) Cat_cat))
  : τ (Transf
      (@test_hom_presheaf_source_action Z x xp s y H)
      (@test_hom_presheaf_source_action Z x xp r y H))
≔ @tapp0_fapp0
    (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat)
    (Functor_cat (Transpose_cat (Hom_cat Z xp y)) Cat_cat)
    (@tapp0_fapp0 (Reverse12_cat Z) Cat_cat _ _ y
      (@fapp1_fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x xp s))
    (@tapp0_fapp0 (Reverse12_cat Z) Cat_cat _ _ y
      (@fapp1_fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x xp r))
    H
    (@tapp0_hom_fapp0 (Reverse12_cat Z) Cat_cat _ _
      (@fapp1_fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x xp s)
      (@fapp1_fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x xp r)
      y
      (@fapp1_fapp0 (Hom_cat (CoOnly2_cat Z) x xp)
        (Hom_cat (Catd_cat (Reverse12_cat Z))
          (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
            (@HomPresheaf_catd_func Z) x)
          (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
            (@HomPresheaf_catd_func Z) xp))
        (@fapp1_func (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
          (@HomPresheaf_catd_func Z) x xp)
        s r alpha));

symbol test_hom_presheaf_source_two_cell_component [Z : Cat]
  (x xp : τ (Obj Z)) (r s : τ (Hom Z x xp))
  (alpha : τ (Hom (Hom_cat Z x xp) r s)) (y : τ (Obj Z))
  (H : τ (Functor (Transpose_cat (Hom_cat Z x y)) Cat_cat))
  (a : τ (Hom Z xp y))
  : τ (Functor
      (fapp0 (@test_hom_presheaf_source_action Z x xp s y H) a)
      (fapp0 (@test_hom_presheaf_source_action Z x xp r y H) a))
≔ @tapp0_fapp0 (Transpose_cat (Hom_cat Z xp y)) Cat_cat
    (@test_hom_presheaf_source_action Z x xp s y H)
    (@test_hom_presheaf_source_action Z x xp r y H)
    a (@test_hom_presheaf_source_two_cell Z x xp r s alpha y H);

flag "print_implicits" off;
flag "print_domains" off;
compute @test_hom_presheaf_source_two_cell_component;
