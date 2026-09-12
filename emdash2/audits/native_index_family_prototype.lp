/* NON-LIBRARY strict-reference whole x-family of the shared native index.
   This tests the next shifted-duality source in a copied preferred prefix.
   It does not qualify the generic lax/Gray profiles or the full kernel. */
require open emdash.native_homd_index_prototype;

// The existing native Hom first varies x over T(Z). Pointwise family O
// shifts that parameter to O(Z), before applying the existing Sigma functor.
symbol native_index_inner_func [Z : Cat] (D : τ (Catd Z))
  : τ (Functor (Op_cat Z) Cat_cat)
≔ @comp_cat_fapp0 (Op_cat Z) (Catd_cat (CoAbove2_cat (@Sigma_cat Z D))) Cat_cat
    (@Sigma_func (CoAbove2_cat (@Sigma_cat Z D)))
    (@comp_cat_fapp0 (Op_cat Z) (CoAbove2_cat (Catd_cat (@Sigma_cat Z D)))
      (Catd_cat (CoAbove2_cat (@Sigma_cat Z D)))
      (@Op_catd_func (@Sigma_cat Z D))
      (@CoAbove2_func (Transpose_cat Z) (Catd_cat (@Sigma_cat Z D))
        (@hom_int Z (@Sigma_cat Z D) (@Sigma_proj1_func Z D))));

// Whole shared-index family over D12(Z), with internal R at its proper source.
symbol native_index_family [Z : Cat] (D : τ (Catd Z))
  : τ (Functor (Reverse12_cat Z) Cat_cat)
≔ @comp_cat_fapp0 (Reverse12_cat Z) (CoAbove3_cat Cat_cat) Cat_cat
    native_homwise_dual
    (@CoAbove3_func (Op_cat Z) Cat_cat (@native_index_inner_func Z D));

symbol native_index_family_point [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  : τ (@= (Obj Cat_cat)
      (@fapp0 (Reverse12_cat Z) Cat_cat (@native_index_family Z D) x)
      (@native_index_cat Z D x))
≔ @eq_refl (Obj Cat_cat) (@native_index_cat Z D x);

// P_D(x)=Fun(S_x(D),Cat) now varies over D2(Z), keeping original D over Z.
symbol native_homd_target_family [Z : Cat] (D : τ (Catd Z))
  : τ (Catd (CoOnly2_cat Z))
≔ @comp_cat_fapp0 (CoOnly2_cat Z) (Transpose_cat Cat_cat) Cat_cat
    (@hom_con Cat_cat Cat_cat Cat_cat (@id_func Cat_cat))
    (@Transpose_func (Reverse12_cat Z) Cat_cat (@native_index_family Z D));

symbol native_homd_target_point [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z))
  : τ (@= (Obj Cat_cat)
      (@fapp0 (CoOnly2_cat Z) Cat_cat (@native_homd_target_family Z D) x)
      (Functor_cat (@native_index_cat Z D x) Cat_cat))
≔ @eq_refl (Obj Cat_cat) (Functor_cat (@native_index_cat Z D x) Cat_cat);

// Whole dimension-1 transpose in the category universe: R after total O,
// with the extra source shift kept visible.
symbol native_transpose_universe : τ (Functor (CoOnly2_cat Cat_cat) Cat_cat)
≔ @comp_cat_fapp0 (CoOnly2_cat Cat_cat) (CoAbove3_cat Cat_cat) Cat_cat
    native_homwise_dual
    (@CoAbove3_func (CoAbove2_cat Cat_cat) Cat_cat op);

symbol native_transpose_family [K : Cat] (E : τ (Catd K))
  : τ (Catd (CoOnly2_cat K))
≔ @comp_cat_fapp0 (CoOnly2_cat K) (CoOnly2_cat Cat_cat) Cat_cat
    native_transpose_universe (@CoOnly2_func K Cat_cat E);

symbol native_transpose_family_point [K : Cat] (E : τ (Catd K)) (x : τ (Obj K))
  : τ (@= (Obj Cat_cat)
      (@fapp0 (CoOnly2_cat K) Cat_cat (@native_transpose_family K E) x)
      (Transpose_cat (Fibre_cat E x)))
≔ @eq_refl (Obj Cat_cat) (Transpose_cat (Fibre_cat E x));

// Category direction checks include the previously invisible third dimension.
assert [C : Cat] (x y : τ (Obj C)) ⊢
  Hom_cat (CoOnly2_cat C) x y ≡ Transpose_cat (Hom_cat C x y);
assert [C : Cat] (x y : τ (Obj C)) (p q : τ (Hom C x y)) ⊢
  Hom_cat (Hom_cat (CoOnly2_cat C) x y) p q ≡ Hom_cat (Hom_cat C x y) q p;
assert [C : Cat] (x y : τ (Obj C)) (p q : τ (Hom C x y))
  (a b : τ (Hom (Hom_cat C x y) q p)) ⊢
  Hom_cat (Hom_cat (Hom_cat (CoOnly2_cat C) x y) p q) a b
  ≡ Hom_cat (Hom_cat (Hom_cat C x y) q p) a b;

assertnot [Z : Cat] (D : τ (Catd Z)) ⊢
  @native_homd_target_family Z D : τ (Catd (CoAbove2_cat Z));
assertnot [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) ⊢
  @fapp0 (CoOnly2_cat K) Cat_cat (@native_transpose_family K E) x
  ≡ Op_cat (Fibre_cat E x);

// Actual whole source action induced by r:x→x', in its contravariant direction.
symbol native_index_source_func [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r : τ (Hom Z x x'))
  : τ (Functor (@native_index_cat Z D x') (@native_index_cat Z D x))
≔ @fapp1_fapp0 (Reverse12_cat Z) Cat_cat (@native_index_family Z D) x' x r;

symbol native_index_source_point [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r : τ (Hom Z x x'))
  (d : τ (Obj (@Sigma_cat Z D)))
  (a : τ (Hom Z x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d)))
  : τ (@= (Obj (@native_index_cat Z D x))
      (@fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x)
        (@native_index_source_func Z D x x' r) (@native_index_point Z D x' d a))
      (@native_index_point Z D x d
        (@comp_fapp0 Z x x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) a r)))
≔ @eq_refl (Obj (@native_index_cat Z D x))
    (@native_index_point Z D x d
      (@comp_fapp0 Z x x' (@fapp0 (@Sigma_cat Z D) Z (@Sigma_proj1_func Z D) d) a r));

// A source 2-cell is retained in the opposite direction, rather than made
// into equality of the two source-action functors.
symbol native_index_source_transf [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r s : τ (Hom Z x x'))
  (alpha : τ (Hom (Hom_cat Z x x') r s))
  : τ (Transf (@native_index_source_func Z D x x' s)
      (@native_index_source_func Z D x x' r))
≔ @fapp1_fapp0 (Hom_cat (Reverse12_cat Z) x' x)
    (Functor_cat (@native_index_cat Z D x') (@native_index_cat Z D x))
    (@fapp1_func (Reverse12_cat Z) Cat_cat (@native_index_family Z D) x' x)
    s r alpha;

// P_D acts on H by precomposition with this same retained source functor.
symbol native_target_source_point [Z : Cat] (D : τ (Catd Z))
  (x x' : τ (Obj Z)) (r : τ (Hom Z x x'))
  (H : τ (Functor (@native_index_cat Z D x) Cat_cat))
  : τ (@= (Functor (@native_index_cat Z D x') Cat_cat)
      (@fapp0 (Functor_cat (@native_index_cat Z D x) Cat_cat)
        (Functor_cat (@native_index_cat Z D x') Cat_cat)
        (@fapp1_fapp0 (CoOnly2_cat Z) Cat_cat (@native_homd_target_family Z D) x x' r) H)
      (@comp_cat_fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x) Cat_cat
        H (@native_index_source_func Z D x x' r)))
≔ @eq_refl (Functor (@native_index_cat Z D x') Cat_cat)
    (@comp_cat_fapp0 (@native_index_cat Z D x') (@native_index_cat Z D x) Cat_cat
      H (@native_index_source_func Z D x x' r));

// Direct new-owner controls and the source shifts that generate the warning
// instances; these do not assert confluence of the inherited prefix.
assert [C : Cat] ⊢ CoAbove3_cat (CoAbove3_cat C) ≡ C;
assert [C : Cat] ⊢ Op_cat (CoAbove3_cat C) ≡ CoAbove3_cat (Op_cat C);
assert [C : Cat] ⊢ CoAbove3_cat (CoAbove2_cat C) ≡ CoAbove2_cat (CoAbove3_cat C);
// Typed 1-arrow views avoid comparing unreduced lambda result classifiers.
symbol native_shift_identity_view [C : Cat] (x : τ (Obj C))
  : τ (Hom C x x) ≔ @id (CoAbove3_cat C) x;
symbol native_shift_composite_view [C : Cat] (x y z : τ (Obj C))
  (f : τ (Hom C x y)) (g : τ (Hom C y z))
  : τ (Hom C x z) ≔ @comp_fapp0 (CoAbove3_cat C) x y z g f;
assert [C : Cat] (x : τ (Obj C)) ⊢ @native_shift_identity_view C x ≡ @id C x;
assert [C : Cat] (x y z : τ (Obj C)) (f : τ (Hom C x y)) (g : τ (Hom C y z)) ⊢
  @native_shift_composite_view C x y z f g ≡ @comp_fapp0 C x y z g f;
assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @CoAbove3_func (CoAbove3_cat A) (CoAbove3_cat B) (@CoAbove3_func A B F) ≡ F;
assert [A B : Cat] (F : τ (Functor A B)) (x y : τ (Obj A)) ⊢
  @fapp1_func (CoAbove3_cat A) (CoAbove3_cat B) (@CoAbove3_func A B F) x y
  ≡ @CoAbove2_func (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)) (@fapp1_func A B F x y);
assert [A B : Cat] ⊢
  @fapp1_func (CoAbove3_cat Cat_cat) Cat_cat native_homwise_dual A B
  ≡ CoAbove2_functor_cat_func A B;
assert [A : Cat] ⊢
  @fapp1_fapp0 (CoAbove3_cat Cat_cat) Cat_cat native_homwise_dual A A
    (@id (CoAbove3_cat Cat_cat) A)
  ≡ @id Cat_cat (CoAbove2_cat A);

assert [C : Cat] (x y : τ (Obj C)) (p q : τ (Hom C x y))
  (a b : τ (Hom (Hom_cat C x y) p q)) ⊢
  Hom_cat (Hom_cat (Hom_cat (CoAbove3_cat C) x y) p q) a b
  ≡ Op_cat (Hom_cat (Hom_cat (Hom_cat C x y) p q) b a);

assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @CoAbove3_func A B
    (@CoAbove3_func (CoAbove3_cat A) (CoAbove3_cat B) (@CoAbove3_func A B F))
  ≡ @CoAbove3_func A B F;
assert [A B : Cat] (F : τ (Functor A B)) ⊢
  @fapp0 (CoAbove2_cat (Functor_cat A B))
    (Functor_cat (CoAbove2_cat A) (CoAbove2_cat B))
    (@fapp1_func (CoAbove3_cat Cat_cat) Cat_cat native_homwise_dual A B) F
  ≡ @CoAbove2_func A B F;
