/* Transport zero composition through the actual object comparisons. */
require open emdash.emdash3_2_additive_categories;
require open emdash.emdash3_2_omega_equiv_cancellation_paths;

symbol pair_comparison_zero_path [C : Cat] (S : τ (@PreadditiveCategory C))
 [A B D A1 B1 D1 : τ (Obj C)]
 (f : τ (Hom C A B)) (g : τ (Hom C B D))
 (f1 : τ (Hom C A1 B1)) (g1 : τ (Hom C B1 D1))
 (c0 : τ (Hom C A A1)) (c1 : τ (Hom C B B1)) (c2 : τ (Hom C D D1))
 (U0 : τ (@OmegaEquivAlong C A A1 c0))
 (p : τ (@= (Hom C A B1) (@comp_fapp0 C A B B1 c1 f) (@comp_fapp0 C A A1 B1 f1 c0)))
 (q : τ (@= (Hom C B D1) (@comp_fapp0 C B D D1 c2 g) (@comp_fapp0 C B B1 D1 g1 c1)))
 (z : τ (@= (Hom C A D) (@comp_fapp0 C A B D g f) (@preadditive_hom_zero C S A D)))
 : τ (@= (Hom C A1 D1) (@comp_fapp0 C A1 B1 D1 g1 f1) (@preadditive_hom_zero C S A1 D1))
≔ @omega_equiv_precomp_reflect_path C A A1 c0 U0 D1 (@comp_fapp0 C A1 B1 D1 g1 f1) (@preadditive_hom_zero
  C S A1 D1)
 (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C A A1 B1 D1 g1 f1 c0)) (@eq_trans _ _ _ _ (@eq_ap (Hom C
  A B1) (Hom C A D1) (λ w : τ (Hom C A B1), (@comp_fapp0 C A B1 D1 g1 w)) _ _ (@eq_sym _ _ _ p))
  (@eq_trans _ _ _ _ (@comp_assoc C A B B1 D1 g1 c1 f) (@eq_trans _ _ _ _ (@eq_ap (Hom C B D1) (Hom C A
  D1) (λ w : τ (Hom C B D1), (@comp_fapp0 C A B D1 w f)) _ _ (@eq_sym _ _ _ q)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc C A B D D1 c2 g f)) (@eq_trans _ _ _ _ (@eq_ap (Hom C A D) (Hom C A D1) (λ w
  : τ (Hom C A D), (@comp_fapp0 C A D D1 c2 w)) _ _ z) (@eq_trans _ _ _ _
  (@preadditive_comp_zero_right_path C S A D D1 c2) (@eq_sym _ _ _ (@preadditive_comp_zero_left_path C S A
  A1 D1 c0)))))))));
