/* Derived ordinary comparison after the original quotient.
   The H-map consumer derives these equations from original whole structure; this adds no universal capability. */
require open emdash.emdash3_2;

symbol comparison_after_quotient_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [Z0 Z1 W0 W1 H0 H1 G0 G1 : τ (Obj C)]
 (q0 : τ (Hom C Z0 H0)) (q1 : τ (Hom C Z1 H1))
 (r0 : τ (Hom C W0 G0)) (r1 : τ (Hom C W1 G1))
 (h : τ (Hom C H0 H1)) (g : τ (Hom C G0 G1))
 (c0 : τ (Hom C H0 G0)) (c1 : τ (Hom C H1 G1))
 (k : τ (Hom C Z0 Z1)) (u : τ (Hom C W0 W1))
 (a0 : τ (Hom C Z0 W0)) (a1 : τ (Hom C Z1 W1))
 (E0 : τ (@= (Hom C Z0 G0) (@comp_fapp0 C Z0 H0 G0 c0 q0) (@comp_fapp0 C Z0 W0 G0 r0 a0)))
 (E1 : τ (@= (Hom C Z1 G1) (@comp_fapp0 C Z1 H1 G1 c1 q1) (@comp_fapp0 C Z1 W1 G1 r1 a1)))
 (Hrec : τ (@= (Hom C Z0 H1) (@comp_fapp0 C Z0 H0 H1 h q0) (@comp_fapp0 C Z0 Z1 H1 q1 k)))
 (Grec : τ (@= (Hom C W0 G1) (@comp_fapp0 C W0 G0 G1 g r0) (@comp_fapp0 C W0 W1 G1 r1 u)))
 (Krec : τ (@= (Hom C Z0 W1) (@comp_fapp0 C Z0 W0 W1 u a0) (@comp_fapp0 C Z0 Z1 W1 a1 k)))
 : τ (@= (Hom C Z0 G1) (@comp_fapp0 C Z0 H0 G1 (@comp_fapp0 C H0 G0 G1 g c0) q0) (@comp_fapp0 C Z0 H0 G1
  (@comp_fapp0 C H0 H1 G1 c1 h) q0))
≔ (@eq_trans _ _ _ _ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C Z0 H0 G0 G1 g c0 q0)) (@eq_trans _ _
  _ _ (@eq_ap (Hom C Z0 G0) (Hom C Z0 G1) (λ cell : τ (Hom C Z0 G0), (@comp_fapp0 C Z0 G0 G1 g cell)) _ _
  E0) (@eq_trans _ _ _ _ (@comp_assoc C Z0 W0 G0 G1 g r0 a0) (@eq_trans _ _ _ _ (@eq_ap (Hom C W0 G1) (Hom
  C Z0 G1) (λ cell : τ (Hom C W0 G1), (@comp_fapp0 C Z0 W0 G1 cell a0)) _ _ Grec) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc C Z0 W0 W1 G1 r1 u a0)) (@eq_trans _ _ _ _ (@eq_ap (Hom C Z0 W1) (Hom C Z0
  G1) (λ cell : τ (Hom C Z0 W1), (@comp_fapp0 C Z0 W1 G1 r1 cell)) _ _ Krec) (@comp_assoc C Z0 Z1 W1 G1 r1
  a1 k))))))) (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C Z0 H0 H1 G1 c1 h q0))
  (@eq_trans _ _ _ _ (@eq_ap (Hom C Z0 H1) (Hom C Z0 G1) (λ cell : τ (Hom C Z0 H1), (@comp_fapp0 C Z0 H1
  G1 c1 cell)) _ _ Hrec) (@eq_trans _ _ _ _ (@comp_assoc C Z0 Z1 H1 G1 c1 q1 k) (@eq_ap (Hom C Z1 G1) (Hom
  C Z0 G1) (λ cell : τ (Hom C Z1 G1), (@comp_fapp0 C Z0 Z1 G1 cell k)) _ _ E1))))));
