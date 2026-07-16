/*
  Reviewer milestone: Product reflexivity provenance.

  Product isomorphism and omega-equivalence constructors retain their
  componentwise evidence heads when both components are reflexive. Their
  projections and decoders still compute componentwise, while the unrelated
  generic reflexive evidence heads remain distinct runtime normal forms.
*/

require open emdash.emdash3_2;

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @idtoiso_cat
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@Struct_sigma
      (@= (Obj A) x x)
      (λ p : τ (@= (Obj A) x x),
        @PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x x p y y)
      (eq_refl x)
      (@pathover_refl (Obj A) (λ _ : τ (Obj A), Obj B) x y))
  ≡ @iso_evidence_product
      A B x x y y
      (@iso_evidence_refl A x)
      (@iso_evidence_refl B y);

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  sigma_Fst
    (@iso_evidence_path
      (Product_cat A B)
      (Struct_sigma x y)
      (Struct_sigma x y)
      (@iso_evidence_product
        A B x x y y
        (@iso_evidence_refl A x)
        (@iso_evidence_refl B y)))
  ≡ @eq_refl (Obj A) x;

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  sigma_Snd
    (@iso_evidence_path
      (Product_cat A B)
      (Struct_sigma x y)
      (Struct_sigma x y)
      (@iso_evidence_product
        A B x x y y
        (@iso_evidence_refl A x)
        (@iso_evidence_refl B y)))
  ≡ @const_pathover
      (Obj A)
      (Obj B)
      x x y y
      (@eq_refl (Obj A) x)
      (@eq_refl (Obj B) y);

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @iso_evidence_product
    A B x x y y
    (@iso_evidence_refl A x)
    (@iso_evidence_refl B y)
  ≡ @iso_evidence_refl
      (Product_cat A B)
      (Struct_sigma x y);

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @omega_equiv_evidence
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@omega_equiv_product
      A B x x y y
      (@omega_equiv_refl A x)
      (@omega_equiv_refl B y))
  ≡ @omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y);

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_left_inv_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_along_left_inv_D0
      (@omega_equiv_along_refl_D0
        (Product_cat A B) (Struct_sigma x y));

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_left_cell_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_product
      (omega_equiv_along_left_cell_D0
        (@omega_equiv_along_refl_D0 A x))
      (omega_equiv_along_left_cell_D0
        (@omega_equiv_along_refl_D0 B y));

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  sigma_Fst
    (omega_equiv_along_path_D1
      (@omega_equiv_along_product_D1
        A B x x y y
        (@id A x) (@id B y)
        (@omega_equiv_along_refl_D0 A x)
        (@omega_equiv_along_refl_D0 B y)))
  ≡ @eq_refl (Obj A) x;

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  sigma_Snd
    (omega_equiv_along_path_D1
      (@omega_equiv_along_product_D1
        A B x x y y
        (@id A x) (@id B y)
        (@omega_equiv_along_refl_D0 A x)
        (@omega_equiv_along_refl_D0 B y)))
  ≡ @const_pathover
      (Obj A)
      (Obj B)
      x x y y
      (@eq_refl (Obj A) x)
      (@eq_refl (Obj B) y);

assert [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @idtoequiv_cat
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@Struct_sigma
      (@= (Obj A) x x)
      (λ p : τ (@= (Obj A) x x),
        @PathOver (Obj A) (λ _ : τ (Obj A), Obj B) x x p y y)
      (eq_refl x)
      (@pathover_refl (Obj A) (λ _ : τ (Obj A), Obj B) x y))
  ≡ @omega_equiv_product
      A B x x y y
      (@omega_equiv_refl A x)
      (@omega_equiv_refl B y);

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @omega_equiv_evidence
    (Product_cat A B)
    (Struct_sigma x y)
    (Struct_sigma x y)
    (@omega_equiv_product
      A B x x y y
      (@omega_equiv_refl A x)
      (@omega_equiv_refl B y))
  ≡ @omega_equiv_along_refl_D0
      (Product_cat A B)
      (Struct_sigma x y);

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_left_cell_D0
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ omega_equiv_along_left_cell_D0
      (@omega_equiv_along_refl_D0
        (Product_cat A B) (Struct_sigma x y));

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  omega_equiv_along_path_D1
    (@omega_equiv_along_product_D1
      A B x x y y
      (@id A x) (@id B y)
      (@omega_equiv_along_refl_D0 A x)
      (@omega_equiv_along_refl_D0 B y))
  ≡ @eq_refl
      (Obj (Product_cat A B))
      (Struct_sigma x y);

assertnot [A B : Cat]
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @omega_equiv_product
    A B x x y y
    (@omega_equiv_refl A x)
    (@omega_equiv_refl B y)
  ≡ @omega_equiv_refl
      (Product_cat A B)
      (Struct_sigma x y);
