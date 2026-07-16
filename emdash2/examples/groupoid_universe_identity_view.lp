/*
  Reviewer example: finite groupoid-universe identity view.

  Public universe equality stays opaque. `GrpdPathView(A,B)` exposes the
  existing TypeEquiv data through named encode/decode maps whose semantic
  owners remain idtoequiv_grpd and grpd_equiv_path.
*/

require open emdash.emdash3_2;

assert [A B : Grpd] ⊢
  @GrpdPathView A B
  ≡ TypeEquiv A B;

assert [A : Grpd] ⊢
  @grpd_path_refl A
  ≡ @type_equiv_refl A;

assert [A : Grpd] ⊢
  type_equiv_to (@grpd_path_refl A)
  ≡ λ x : τ A, x;

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_path_encode A B p
  ≡ @idtoequiv_grpd A B p;

assert [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  @grpd_path_decode A B e
  ≡ @grpd_equiv_path A B e;

assert [A : Grpd] ⊢
  @grpd_path_encode A A (@eq_refl Grpd_grpd A)
  ≡ @grpd_path_refl A;

assert [A : Grpd] ⊢
  @grpd_path_decode A A (@grpd_path_refl A)
  ≡ @eq_refl Grpd_grpd A;

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_path_decode_encode A B p
  : τ (
      @grpd_path_decode A B (@grpd_path_encode A B p)
      = p);

assert [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  @grpd_path_encode_decode A B e
  : τ (
      @grpd_path_encode A B (@grpd_path_decode A B e)
      = e);

assert [A B : Grpd]
  (e : τ (@GrpdPathView A B))
  (a : τ A) ⊢
  @grpd_path_decode_coe A B e a
  : τ (
      @coe_grpd A B (@grpd_path_decode A B e) a
      = type_equiv_to e a);

// Product paths retain the promoted componentwise decoder computation.
assert [A A' B B' : Grpd]
  (eA : τ (@GrpdPathView A A'))
  (eB : τ (@GrpdPathView B B')) ⊢
  @grpd_path_decode
    (Product_grpd A B)
    (Product_grpd A' B')
    (@product_type_equiv A A' B B' eA eB)
  ≡ @product_grpd_path
      A A' B B'
      (@grpd_path_decode A A' eA)
      (@const_pathover
        Grpd_grpd Grpd_grpd A A' B B'
        (@grpd_path_decode A A' eA)
        (@grpd_path_decode B B' eB));

// The existing decoder theorem supplies nontrivial Pi action under the view.
assert [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (@GrpdPathView (B x) (C x)))
  (f : τ (@Pi_grpd A B))
  (x : τ A) ⊢
  @grpd_equiv_path_pi_action A B C e f x
  : τ (
      (@coe_grpd
        (@Pi_grpd A B)
        (@Pi_grpd A C)
        (@grpd_path_decode
          (@Pi_grpd A B)
          (@Pi_grpd A C)
          (@pi_type_equiv_same_domain A B C e))
        f)
        x
      = type_equiv_to (e x) (f x));

// Same-base Sigma equivalence is accepted without a second decoder body.
assert [A : Grpd]
  [P Q : τ A → Grpd]
  (e : Π x : τ A, τ (@GrpdPathView (P x) (Q x))) ⊢
  @grpd_path_decode
    (@Σ_ A P)
    (@Σ_ A Q)
    (@sigma_type_equiv_same_base A P Q e)
  : τ (@= Grpd_grpd (@Σ_ A P) (@Σ_ A Q));

// The named view remains finite at the current unstratified self-universe.
assert ⊢
  @grpd_path_refl Grpd_grpd
  : τ (@GrpdPathView Grpd_grpd Grpd_grpd);

assertnot [A B : Grpd] ⊢
  @= Grpd_grpd A B
  ≡ @GrpdPathView A B;

assertnot [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  e
  : τ (@= Grpd_grpd A B);

assertnot [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_path_decode A B (@grpd_path_encode A B p)
  ≡ p;

assertnot [A B : Grpd]
  (e : τ (@GrpdPathView A B)) ⊢
  @grpd_path_encode A B (@grpd_path_decode A B e)
  ≡ e;

assertnot [A B : Grpd]
  (e : τ (@GrpdPathView A B))
  (a : τ A) ⊢
  @coe_grpd A B (@grpd_path_decode A B e) a
  ≡ type_equiv_to e a;
