/* Constructor congruence in the actual target groupoid. */
require open emdash.emdash3_2;

// Dependent constructor congruence when the last fibre is a proposition.
// The result stays in the constructor's actual codomain Z.
symbol two_prop_fibre_image_path [A B Z : Grpd] (P : τ A → τ B → Grpd)
  (c : Π a0 : τ A, Π b0 : τ B, τ (P a0 b0) → τ Z)
  (hP : Π a0 : τ A, Π b0 : τ B, τ (IsPropGrpd (P a0 b0)))
  [a : τ A] [b : τ B] (u : τ (P a b))
  [a1 : τ A] [b1 : τ B] (v : τ (P a1 b1))
  (p : τ (@= A a a1)) (q : τ (@= B b b1))
  : τ (@= Z (c a b u) (c a1 b1 v))
≔ (@ind_eq A a1 a (@eq_sym A a a1 p)
    (λ a0 : τ A, @Pi_grpd B (λ b0 : τ B,
      @Pi_grpd (P a0 b0) (λ v0 : τ (P a0 b0),
        @Pi_grpd (@= B b b0) (λ q0 : τ (@= B b b0),
          @= Z (c a b u) (c a0 b0 v0)))))
    (λ b0 : τ B, λ v0 : τ (P a b0), λ q0 : τ (@= B b b0),
      (@ind_eq B b0 b (@eq_sym B b b0 q0)
        (λ b2 : τ B, @Pi_grpd (P a b2) (λ v2 : τ (P a b2),
          @= Z (c a b u) (c a b2 v2)))
        (λ v2 : τ (P a b),
          @eq_ap (P a b) Z (c a b) u v2
            (@is_contr_center (@= (P a b) u v2) (hP a b u v2)))) v0)) b1 v q;
