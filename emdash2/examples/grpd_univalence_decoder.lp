/*
  Reviewer milestone: operational groupoid decoder coherence.

  The decoder-oriented capability supplies both propositional round trips and
  derives the canonical contractible-fibre univalence capability. Transport
  along the operational decoder agrees propositionally with the forward map;
  the broad runtime rule and arbitrary legacy-ua agreement remain absent.
*/

require open emdash.emdash3_2;

assert ⊢
  grpd_univalence_from_decoder
  : τ GrpdUnivalence;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @grpd_univalence_selected_path A B e
  ≡ @grpd_equiv_path A B e;

assert [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_equiv_path_idtoequiv A B p
  : τ (
      @grpd_equiv_path A B (@idtoequiv_grpd A B p)
      = p);

assert [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @idtoequiv_grpd_equiv_path A B e
  : τ (
      @idtoequiv_grpd A B (@grpd_equiv_path A B e)
      = e);

assert [A : Grpd]
  (a : τ A) ⊢
  @coe_grpd_idtoequiv A A (eq_refl A) a
  ≡ @eq_refl A a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  @grpd_equiv_path_coe A B e a
  : τ (
      @coe_grpd A B (@grpd_equiv_path A B e) a
      = type_equiv_to e a);

assert [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (B x) (C x)))
  (f : τ (@Pi_grpd A B))
  (x : τ A) ⊢
  @grpd_equiv_path_pi_action A B C e f x
  : τ (
      (@coe_grpd
        (@Pi_grpd A B)
        (@Pi_grpd A C)
        (@grpd_equiv_path
          (@Pi_grpd A B)
          (@Pi_grpd A C)
          (@pi_type_equiv_same_domain A B C e))
        f)
        x
      = type_equiv_to (e x) (f x));

assert [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B'))
  (x : τ A)
  (y : τ B) ⊢
  @grpd_equiv_path_coe
    (Product_grpd A B)
    (Product_grpd A' B')
    (@product_type_equiv A A' B B' eA eB)
    (@Product_pair_grpd A B x y)
  : τ (
      @coe_grpd
        (Product_grpd A B)
        (Product_grpd A' B')
        (@grpd_equiv_path
          (Product_grpd A B)
          (Product_grpd A' B')
          (@product_type_equiv A A' B B' eA eB))
        (@Product_pair_grpd A B x y)
      = @Product_pair_grpd A' B'
          (type_equiv_to eA x)
          (type_equiv_to eB y));

assertnot [A B : Grpd]
  (p : τ (@= Grpd_grpd A B)) ⊢
  @grpd_equiv_path A B (@idtoequiv_grpd A B p)
  ≡ p;

assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @idtoequiv_grpd A B (@grpd_equiv_path A B e)
  ≡ e;

assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  @coe_grpd A B (@grpd_equiv_path A B e) a
  ≡ type_equiv_to e a;

assertnot (U : τ GrpdUnivalence)
  [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @ua_grpd U A B e
  ≡ @grpd_equiv_path A B e;
