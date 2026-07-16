/*
  Reviewer milestone: ordinary Pi happly/funext compatibility.

  A structured dependent-function path has a diagonal pointwise observation,
  and pointwise paths extend to arbitrary related inputs by base-path
  induction. The forward round trip computes pointwise. The reverse round
  trip is propositional, with its reflexive base supplied by the selected
  proof-time Pi coherence law. The two maps are packaged as a contractible-
  fibre TypeEquiv through the reviewed quasi-inverse theorem capability.
*/

require open emdash.emdash3_2;

assert [A : Grpd]
  [B : τ A → Grpd]
  (f g : Π x : τ A, τ (B x)) ⊢
  @PiPointwisePath A B f g
  ≡ @Pi_grpd A (λ x : τ A, f x = g x);

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g))
  (x : τ A) ⊢
  @PiHapply A B f g p x
  ≡ p x x (@eq_refl A x);

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g))
  (x0 x1 : τ A)
  (p : τ (x0 = x1)) ⊢
  @PiFunext A B f g h x0 x1 p
  ≡ @ind_eqr A x1
      (λ x0 : τ A, λ p : τ (x0 = x1),
        @PathOver A B x0 x1 p (f x0) (g x1))
      (h x1)
      x0
      p;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g))
  (x : τ A) ⊢
  @PiHapply A B f g (@PiFunext A B f g h) x
  ≡ h x;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  @pi_funext_eta A B f g p
  : τ (@PiFunext A B f g (@PiHapply A B f g p) = p);

// Typed reflexivity exercises the proof-time base equation; it does not claim
// that the two stable heads are runtime-convertible.
assert [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x)) ⊢
  @eq_refl
    (@= (@Pi_grpd A B) f f)
    (@eq_refl (@Pi_grpd A B) f)
  : τ (
      @PiFunext A B f f
        (@PiHapply A B f f (@eq_refl (@Pi_grpd A B) f))
      = @eq_refl (@Pi_grpd A B) f);

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)] ⊢
  @pi_happly_type_equiv A B f g
  : τ (TypeEquiv
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g));

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  type_equiv_to (@pi_happly_type_equiv A B f g) p
  ≡ @PiHapply A B f g p;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  type_equiv_from (@pi_happly_type_equiv A B f g) h
  ≡ @PiFunext A B f g h;

assert [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g)) ⊢
  type_equiv_right (@pi_happly_type_equiv A B f g) h
  ≡ @pi_happly_beta A B f g h;

assertnot [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g)) ⊢
  @PiFunext A B f g (@PiHapply A B f g p)
  ≡ p;
