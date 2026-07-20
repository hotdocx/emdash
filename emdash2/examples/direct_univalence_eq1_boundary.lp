/*
  Reviewer example: measured direct-univalence boundary for equality-valued.

  Cat and Grpd have rigid runtime equality-valued normal forms. An abstract category uses
  proof-time comparison. A single stable carrier view supports explicit
  transparent identity casts after specialization. Product equality retains a
  stable path view, while Product/opposite compatibility names route through
  the general casts. Facade observations still require an explicit package;
  no opaque term operation is inserted.
*/

require open emdash.emdash3_2;

// The abstract comparison fires through typed reflexivity in both directions.
assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @eq_refl (@OmegaEquiv C x y) p
  : τ (@= (@OmegaEquiv C x y) p p);

assert [C : Cat] (x y : τ (Obj C))
  (e : τ (@OmegaEquiv C x y)) ⊢
  @eq_refl (@= (Obj C) x y) e
  : τ (@= (@= (Obj C) x y) e e);

assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @= (Obj C) x y
  ≡ @OmegaEquiv C x y;

// Explicit casts use one stable carrier view and have definitional round trips.
assert [C : Cat] [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_cast_to_object_path C x y
    (@object_path_cast_to_omega C x y p)
  ≡ p;

assert [C : Cat] [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y)) ⊢
  @object_path_cast_to_omega C x y
    (@omega_cast_to_object_path C x y e)
  ≡ e;

// The two rigid universe owners select equality-valued at runtime.
assert [A B : Cat] ⊢
  @= (Obj Cat_cat) A B
  ≡ @OmegaEquiv Cat_cat A B;

assert [A B : Grpd] ⊢
  @= (Obj Grpd_cat) A B
  ≡ @OmegaEquiv Grpd_cat A B;

// The retained theorem-level groupoid TypeEquiv view remains separate from
// the rigid native universe equality normal form.
assertnot [A B : Grpd] ⊢
  @= (Obj Grpd_cat) A B
  ≡ @GrpdPathView A B;

// Explicit equality-valued reflexivity exposes its selected universe arrows.
assert [A : Cat] ⊢
  @omega_equiv_to Cat_cat A A
    (@omega_equiv_refl Cat_cat A)
  ≡ @id_func A;

assert [A : Grpd] ⊢
  @omega_equiv_to Grpd_cat A A
    (@omega_equiv_refl Grpd_cat A)
  ≡ @id Grpd_cat A;

// Product equality retains a stable classifier whose carrier is the familiar
// constant-family Sigma path data.
assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B))) ⊢
  @= (Obj (Product_cat A B)) x y
  ≡ @ProductPathView (Obj A) (Obj B) x y;

assert [A B : Grpd]
  (x y : τ (Product_grpd A B)) ⊢
  τ (@ProductPathView A B x y)
  ≡ τ (@SigmaPathView A (λ _ : τ A, B) x y);

// The named Product casts are transparent identities with definitional round
// trips, but they do not turn a raw path into an observable facade package.
assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @product_omega_as_path A B x y
    (@product_path_as_omega A B x y p)
  ≡ p;

assertnot [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @omega_equiv_to
    (Product_cat A B) x y
    (@product_path_as_omega A B x y p)
  ≡ @path_to_hom (Product_cat A B) x y p;

assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @omega_equiv_to
    (Product_cat A B) x y
    (@object_path_equiv (Product_cat A B) x y p)
  ≡ @path_to_hom (Product_cat A B) x y p;

// Opposite object reduction uses the same general carrier view. A raw path is
// not silently accepted; the named adapter supplies the explicit cast.
assert [A : Cat]
  (x y : τ (Obj A)) ⊢
  τ (@ObjectPathCastView (Op_cat A) x y)
  ≡ τ (@= (Obj A) x y);

assertnot [A : Cat]
  (x y : τ (Obj (Op_cat A)))
  (p : τ (@= (Obj (Op_cat A)) x y)) ⊢
  p : τ (@OmegaEquiv (Op_cat A) x y);

assert [A : Cat]
  (x y : τ (Obj A))
  (p : τ (@= (Obj A) x y)) ⊢
  @op_omega_as_path A x y
    (@op_path_as_omega A x y p)
  ≡ p;

assertnot [A : Cat]
  (x y : τ (Obj A))
  (p : τ (@= (Obj A) x y)) ⊢
  @omega_equiv_to
    (Op_cat A) x y
    (@op_path_as_omega A x y p)
  ≡ @path_to_hom (Op_cat A) x y p;

assert [A : Cat]
  (x y : τ (Obj (Op_cat A)))
  (p : τ (@= (Obj (Op_cat A)) x y)) ⊢
  @omega_equiv_to
    (Op_cat A) x y
    (@object_path_equiv (Op_cat A) x y p)
  ≡ @path_to_hom (Op_cat A) x y p;

// The general identity casts remain stable when the underlying category is a
// reduction-heavy Product or a literal path category.
assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @op_omega_as_path (Product_cat A B) x y
    (@op_path_as_omega (Product_cat A B) x y p)
  ≡ p;

assert [A : Grpd]
  (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @op_omega_as_path (Path_cat A) x y
    (@op_path_as_omega (Path_cat A) x y p)
  ≡ p;

// Raw generic reflexivity remains distinct from the explicit facade package.
assertnot [A : Cat] ⊢
  @omega_equiv_to
    Cat_cat A A (@eq_refl (Obj Cat_cat) A)
  ≡ @id_func A;
