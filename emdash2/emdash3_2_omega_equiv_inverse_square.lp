require open emdash.emdash3_2_omega_equiv_cancellation_paths;

// Derive inverse compatibility using the existing selected inverses and cancellation.
symbol omega_equiv_inverse_square_path [C : Cat] [A0 A1 B0 B1 : τ (Obj C)]
 (f0 : τ (Hom C A0 B0)) (f1 : τ (Hom C A1 B1))
 (u : τ (Hom C A0 A1)) (v : τ (Hom C B0 B1))
 (U : τ (@OmegaEquivAlong C A0 A1 u)) (V : τ (@OmegaEquivAlong C B0 B1 v))
 (p : τ (@= (Hom C A0 B1) (@comp_fapp0 C A0 B0 B1 v f0) (@comp_fapp0 C A0 A1 B1 f1 u)))
 : τ (@= (Hom C A1 B0)
   (@comp_fapp0 C A1 B1 B0 (@omega_equiv_along_left_inv C B0 B1 v V) f1)
   (@comp_fapp0 C A1 A0 B0 f0 (@omega_equiv_along_left_inv C A0 A1 u U)))
≔ let iu : τ (Hom C A1 A0) ≔ @omega_equiv_along_left_inv C A0 A1 u U in
  let iv : τ (Hom C B1 B0) ≔ @omega_equiv_along_left_inv C B0 B1 v V in
  @omega_equiv_precomp_reflect_path C A0 A1 u U B0
    (@comp_fapp0 C A1 B1 B0 iv f1) (@comp_fapp0 C A1 A0 B0 f0 iu)
    (@eq_trans _ _ _ _
      (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C A0 A1 B1 B0 iv f1 u))
        (@eq_trans _ _ _ _
          (@eq_ap (Hom C A0 B1) (Hom C A0 B0) (λ h : τ (Hom C A0 B1), @comp_fapp0 C A0 B1 B0 iv h) _ _
  (@eq_sym
  _ _ _ p))
          (@eq_trans _ _ _ _ (@comp_assoc C A0 B0 B1 B0 iv v f0)
            (@eq_ap (Hom C B0 B0) (Hom C A0 B0) (λ h : τ (Hom C B0 B0), @comp_fapp0 C A0 B0 B0 h f0) _ _
              (@omega_equiv_along_left_law C B0 B1 v V)))))
      (@eq_sym _ _ _
        (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C A0 A1 A0 B0 f0 iu u))
          (@eq_ap (Hom C A0 A0) (Hom C A0 B0) (λ h : τ (Hom C A0 A0), @comp_fapp0 C A0 A0 B0 f0 h) _ _
            (@omega_equiv_along_left_law C A0 A1 u U)))));
