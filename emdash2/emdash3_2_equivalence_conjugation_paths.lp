/* The public connecting arrow is the original δ conjugated by its endpoint comparisons. */
require open emdash.emdash3_2_eq1_evidence_property;

symbol conjugated_arrow_source_path [C : Cat] [A B X Y : τ (Obj C)]
 (d : τ (Hom C A B)) (c0 : τ (Hom C A X)) (c1 : τ (Hom C B Y))
 (U0 : τ (@OmegaEquivAlong C A X c0))
 : τ (@= (Hom C A Y)
 (@comp_fapp0 C A X Y
   (@comp_fapp0 C X B Y c1 (@comp_fapp0 C X A B d (@omega_equiv_along_left_inv C A X c0 U0))) c0)
 (@comp_fapp0 C A B Y c1 d))
≔ @eq_trans _ _ _ _
 (@eq_sym _ _ _ (@comp_assoc C A X B Y c1
   (@comp_fapp0 C X A B d (@omega_equiv_along_left_inv C A X c0 U0)) c0))
 (@eq_ap (Hom C A B) (Hom C A Y)
  (λ f : τ (Hom C A B), @comp_fapp0 C A B Y c1 f) _ _
  (@eq_trans _ _ _ _
   (@eq_sym _ _ _ (@comp_assoc C A X A B d (@omega_equiv_along_left_inv C A X c0 U0) c0))
   (@eq_ap (Hom C A A) (Hom C A B)
    (λ f : τ (Hom C A A), @comp_fapp0 C A A B d f) _ _
    (@omega_equiv_along_left_law C A X c0 U0))));
