/* Fixed-forward two-of-three with computational inverse data retained. */
require open emdash.emdash3_2_omega_equiv_composition;

// Two existing equivalences and the actual composite equation determine the right factor.
symbol omega_equiv_right_factor [C : Cat] [A B D : τ (Obj C)]
 (m : τ (Hom C A B)) (f : τ (Hom C A D)) (g : τ (Hom C B D))
 (M : τ (@OmegaEquivAlong C A B m)) (F : τ (@OmegaEquivAlong C A D f))
 (p : τ (@= (Hom C A D) (@comp_fapp0 C A B D g m) f))
 : τ (@OmegaEquivAlong C B D g)
≔ let inv : τ (Hom C B A) ≔ @omega_equiv_along_left_inv C A B m M in
  let inv_equiv : τ (@OmegaEquivAlong C B A inv) ≔ @omega_equiv_along_intro C B A inv m m
    (@omega_equiv_left_as_right_law C A B m M) (@omega_equiv_along_left_law C A B m M) in
  @omega_equiv_along_equal C B D (@comp_fapp0 C B A D f inv) g
    (@omega_equiv_along_comp C B A D inv f inv_equiv F)
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C A D) (Hom C B D) (λ v : τ (Hom C A D), @comp_fapp0 C B A D v inv) _ _
        (@eq_sym _ _ _ p))
      (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C B A B D g m inv))
        (@eq_ap (Hom C B B) (Hom C B D) (λ v : τ (Hom C B B), @comp_fapp0 C B B D g v) _ _
          (@omega_equiv_left_as_right_law C A B m M))));
