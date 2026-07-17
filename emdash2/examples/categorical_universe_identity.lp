/*
  Reviewer example: direct categorical-universe identity.

  Category-universe equality now exposes the stable equality-valued EQ1
  facade. The former D0 `CatPathView` remains an explicit compatibility view;
  generic eq_refl is retained for literal J and eq_ap computation.
*/

require open emdash.emdash3_2;

assert [A B : Cat] ⊢
  @= (Obj Cat_cat) A B
  ≡ @OmegaEquiv_EQ1 Cat_cat A B;

assertnot [A B : Cat] ⊢
  @= (Obj Cat_cat) A B
  ≡ @CatPathView A B;

assert [A B : Cat] ⊢
  @CatPathView A B
  ≡ OmegaEquiv Cat_cat A B;

assert [A : Cat] ⊢
  @omega_equiv_refl_EQ1 Cat_cat A
  : τ (@= (Obj Cat_cat) A A);

assert [A : Cat] ⊢
  @omega_equiv_to_EQ1 Cat_cat A A
    (@omega_equiv_refl_EQ1 Cat_cat A)
  ≡ @id_func A;

assert [A : Cat] ⊢
  @omega_equiv_evidence_EQ1 Cat_cat A A
    (@omega_equiv_refl_EQ1 Cat_cat A)
  ≡ @omega_equiv_along_refl_EQ1 Cat_cat A;

assert [A : Cat] ⊢
  @omega_equiv_D0_to_EQ1 Cat_cat A A (@cat_path_refl A)
  ≡ @omega_equiv_refl_EQ1 Cat_cat A;

assert [A : Cat] ⊢
  @cat_path_functor A A (@cat_path_refl A)
  ≡ @id_func A;

assert [A : Cat] ⊢
  @cat_path_evidence A A (@cat_path_refl A)
  ≡ @omega_equiv_along_refl_D0 Cat_cat A;

assert [A : Cat] ⊢
  @cat_path_encode A A (@eq_refl (Obj Cat_cat) A)
  ≡ @cat_path_refl A;

assert [A : Cat] ⊢
  @cat_path_decode A A (@cat_path_refl A)
  ≡ @eq_refl (Obj Cat_cat) A;

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_decode_encode A B p
  : τ (
      @cat_path_decode A B (@cat_path_encode A B p)
      = p);

assert [A B : Cat]
  (e : τ (@CatPathView A B)) ⊢
  @cat_path_encode_decode A B e
  : τ (
      @cat_path_encode A B (@cat_path_decode A B e)
      = e);

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_encode_functor A B p
  : τ (
      @cat_path_functor A B (@cat_path_encode A B p)
      = @path_to_hom Cat_cat A B p);

assert [A B : Cat] ⊢
  @cat_path_product
    A A B B (@cat_path_refl A) (@cat_path_refl B)
  ≡ @cat_path_refl (Product_cat A B);

assert [A B : Cat]
  (e : τ (@CatPathView A B))
  (x y : τ (Obj A)) ⊢
  @cat_path_fapp1 A B e x y
  : τ (OmegaEquiv
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (cat_path_functor e) x)
        (@fapp0 A B (cat_path_functor e) y)));

assert [A : Cat]
  (x y : τ (Obj A)) ⊢
  @omega_equiv_to
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat A x y)
    (@cat_path_fapp1 A A (@cat_path_refl A) x y)
  ≡ @id_func (Hom_cat A x y);

assert ⊢
  @= (Obj Cat_cat) Cat_cat Cat_cat
  ≡ @OmegaEquiv_EQ1 Cat_cat Cat_cat Cat_cat;

assert ⊢
  @cat_path_refl Cat_cat
  : τ (@CatPathView Cat_cat Cat_cat);

assert [A : Cat] ⊢
  @ind_eqr
    (Obj Cat_cat)
    A
    (λ X : Cat, λ _ : τ (@= (Obj Cat_cat) X A), Unit_grpd)
    tt
    A
    (@eq_refl (Obj Cat_cat) A)
  ≡ tt;

assertnot [A : Cat] ⊢
  @eq_refl (Obj Cat_cat) A
  ≡ @omega_equiv_refl_EQ1 Cat_cat A;

assertnot [A : Cat] ⊢
  @omega_equiv_to_EQ1
    Cat_cat A A (@eq_refl (Obj Cat_cat) A)
  ≡ @id_func A;

assertnot [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B)) ⊢
  @cat_path_decode A B (@cat_path_encode A B p)
  ≡ p;

assertnot [A B : Cat]
  (e : τ (@CatPathView A B)) ⊢
  @cat_path_encode A B (@cat_path_decode A B e)
  ≡ e;

assertnot [A : Cat] ⊢
  @ind_eqr
    (Obj Cat_cat)
    A
    (λ X : Cat, λ _ : τ (@= (Obj Cat_cat) X A), Unit_grpd)
    tt
    A
    (@omega_equiv_refl_EQ1 Cat_cat A)
  ≡ tt;

assertnot [A : Cat]
  (x y : τ (Obj A)) ⊢
  @cat_path_fapp1 A A (@cat_path_refl A) x y
  ≡ @omega_equiv_refl Cat_cat (Hom_cat A x y);
