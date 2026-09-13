/* NON-LIBRARY controls for the copied HomPresheaf candidate. */
/* TEST ONLY: nonidentity whole source action of the repaired classifier.
   The helper definitions are observations used by the assertions below. */
require open emdash.emdash3_2;

symbol test_hom_presheaf_source_action [Z : Cat]
  (x xp : τ (Obj Z)) (r : τ (Hom Z x xp)) (y : τ (Obj Z))
  (H : τ (Functor (Transpose_cat (Hom_cat Z x y)) Cat_cat))
  : τ (Functor (Transpose_cat (Hom_cat Z xp y)) Cat_cat)
≔ fapp0
    (@tapp0_fapp0 (Reverse12_cat Z) Cat_cat
      (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x)
      (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) xp)
      y
      (@fapp1_fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x xp r)) H;

symbol test_hom_presheaf_source_action_expected [Z : Cat]
  (x xp : τ (Obj Z)) (r : τ (Hom Z x xp)) (y : τ (Obj Z))
  (H : τ (Functor (Transpose_cat (Hom_cat Z x y)) Cat_cat))
  : τ (Functor (Transpose_cat (Hom_cat Z xp y)) Cat_cat)
≔ @hom_precomp_along_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
    Cat_cat
    (Transpose_cat (Hom_cat Z xp y)) (Transpose_cat (Hom_cat Z x y))
    (@Transpose_func (Hom_cat Z xp y) (Hom_cat Z x y)
      (@Hom_func Z xp x y y r (@id Z y))) H;

// Runtime keeps the existing rigid two-endpoint Hom owner.

assert ⊢ @test_hom_presheaf_source_action
  ≡ @test_hom_presheaf_source_action_expected;

// TEST ONLY: first use the existing Hom/precomposition comparison at its
// own head, then apply ordinary equality congruence through the dual/action
// context. This does not add a unifier for the larger expression.
assert [Z : Cat] (x xp : τ (Obj Z)) (r : τ (Hom Z x xp)) (y : τ (Obj Z))
  (H : τ (Functor (Transpose_cat (Hom_cat Z x y)) Cat_cat)) ⊢
  @eq_ap
    (Functor (Hom_cat Z xp y) (Hom_cat Z x y))
    (Functor (Transpose_cat (Hom_cat Z xp y)) Cat_cat)
    (λ F : τ (Functor (Hom_cat Z xp y) (Hom_cat Z x y)),
      @hom_precomp_along_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
        Cat_cat (Transpose_cat (Hom_cat Z xp y)) (Transpose_cat (Hom_cat Z x y))
        (@Transpose_func (Hom_cat Z xp y) (Hom_cat Z x y) F) H)
    (@Hom_func Z xp x y y r (@id Z y))
    (@hom_precomp_along_func Z Z (@id_func Z) y x xp r)
    (@eq_refl (Functor (Hom_cat Z xp y) (Hom_cat Z x y))
      (@Hom_func Z xp x y y r (@id Z y)))
  : τ (@= (Functor (Transpose_cat (Hom_cat Z xp y)) Cat_cat)
      (@test_hom_presheaf_source_action Z x xp r y H)
      (@hom_precomp_along_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
        Cat_cat (Transpose_cat (Hom_cat Z xp y)) (Transpose_cat (Hom_cat Z x y))
        (@Transpose_func (Hom_cat Z xp y) (Hom_cat Z x y)
          (@hom_precomp_along_func Z Z (@id_func Z) y x xp r)) H));

symbol test_hom_presheaf_target_action [Z : Cat]
  (x y yp : τ (Obj Z)) (s : τ (Hom Z y yp))
  (H : τ (Functor (Transpose_cat (Hom_cat Z x yp)) Cat_cat))
  : τ (Functor (Transpose_cat (Hom_cat Z x y)) Cat_cat)
≔ fapp0
    (@fapp1_fapp0 (Reverse12_cat Z) Cat_cat
      (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x)
      yp y s) H;

symbol test_hom_presheaf_target_action_expected [Z : Cat]
  (x y yp : τ (Obj Z)) (s : τ (Hom Z y yp))
  (H : τ (Functor (Transpose_cat (Hom_cat Z x yp)) Cat_cat))
  : τ (Functor (Transpose_cat (Hom_cat Z x y)) Cat_cat)
≔ @hom_precomp_along_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
    Cat_cat
    (Transpose_cat (Hom_cat Z x y)) (Transpose_cat (Hom_cat Z x yp))
    (@Transpose_func (Hom_cat Z x y) (Hom_cat Z x yp)
      (@Hom_func Z x x y yp (@id Z x) s)) H;

assert ⊢ @test_hom_presheaf_target_action
  ≡ @test_hom_presheaf_target_action_expected;
