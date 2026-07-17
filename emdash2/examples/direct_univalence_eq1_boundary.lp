/*
  Reviewer example: measured direct-univalence boundary for EQ1.

  Cat and Grpd have rigid runtime EQ1 normal forms. An abstract category uses
  proof-time comparison. Reduction-heavy concrete formers may require the
  explicit object_path_equiv_EQ1 package; no opaque cast is inserted.
*/

require open emdash.emdash3_2;

// The abstract comparison fires through typed reflexivity in both directions.
assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @eq_refl (@OmegaEquiv_EQ1 C x y) p
  : τ (@= (@OmegaEquiv_EQ1 C x y) p p);

assert [C : Cat] (x y : τ (Obj C))
  (e : τ (@OmegaEquiv_EQ1 C x y)) ⊢
  @eq_refl (@= (Obj C) x y) e
  : τ (@= (@= (Obj C) x y) e e);

assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @= (Obj C) x y
  ≡ @OmegaEquiv_EQ1 C x y;

// The two rigid universe owners select EQ1 at runtime.
assert [A B : Cat] ⊢
  @= (Obj Cat_cat) A B
  ≡ @OmegaEquiv_EQ1 Cat_cat A B;

assert [A B : Grpd] ⊢
  @= (Obj Grpd_cat) A B
  ≡ @OmegaEquiv_EQ1 Grpd_cat A B;

assertnot [A B : Cat] ⊢
  @= (Obj Cat_cat) A B
  ≡ @CatPathView A B;

assertnot [A B : Grpd] ⊢
  @= (Obj Grpd_cat) A B
  ≡ @GrpdPathView A B;

// Explicit EQ1 reflexivity exposes its selected universe arrows.
assert [A : Cat] ⊢
  @omega_equiv_to_EQ1 Cat_cat A A
    (@omega_equiv_refl_EQ1 Cat_cat A)
  ≡ @id_func A;

assert [A : Grpd] ⊢
  @omega_equiv_to_EQ1 Grpd_cat A A
    (@omega_equiv_refl_EQ1 Grpd_cat A)
  ≡ @id Grpd_cat A;

// Product equality has already decoded to a transparent Sigma path, so raw
// silent interchange is unavailable. The explicit semantic adapter computes.
assertnot [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  p : τ (@OmegaEquiv_EQ1 (Product_cat A B) x y);

assert [A B : Cat]
  (x y : τ (Obj (Product_cat A B)))
  (p : τ (@= (Obj (Product_cat A B)) x y)) ⊢
  @omega_equiv_to_EQ1
    (Product_cat A B) x y
    (@object_path_equiv_EQ1 (Product_cat A B) x y p)
  ≡ @path_to_hom (Product_cat A B) x y p;

// Opposite object reduction has the same explicit-adapter boundary.
assertnot [A : Cat]
  (x y : τ (Obj (Op_cat A)))
  (p : τ (@= (Obj (Op_cat A)) x y)) ⊢
  p : τ (@OmegaEquiv_EQ1 (Op_cat A) x y);

assert [A : Cat]
  (x y : τ (Obj (Op_cat A)))
  (p : τ (@= (Obj (Op_cat A)) x y)) ⊢
  @omega_equiv_to_EQ1
    (Op_cat A) x y
    (@object_path_equiv_EQ1 (Op_cat A) x y p)
  ≡ @path_to_hom (Op_cat A) x y p;

// Raw generic reflexivity remains distinct from the explicit facade package.
assertnot [A : Cat] ⊢
  @omega_equiv_to_EQ1
    Cat_cat A A (@eq_refl (Obj Cat_cat) A)
  ≡ @id_func A;
