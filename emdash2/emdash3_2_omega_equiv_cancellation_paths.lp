/* Whole composition cancellation from the existing fixed-forward evidence. */
require open emdash.emdash3_2;

// Cancel f after maps into its source, using the supplied left inverse law.
symbol omega_equiv_postcomp_reflect_path [C : Cat] [a b : τ (Obj C)]
  (f : τ (Hom C a b)) (E : τ (@OmegaEquivAlong C a b f)) (z : τ (Obj C))
  (u v : τ (Hom C z a))
  (p : τ (@= (Hom C z b) (@comp_fapp0 C z a b f u) (@comp_fapp0 C z a b f v)))
  : τ (@= (Hom C z a) u v)
≔ let l : τ (Hom C b a) ≔ @omega_equiv_along_left_inv C a b f E in
  @eq_trans (Hom C z a) u (@comp_fapp0 C z a a (@comp_fapp0 C a b a l f) u) v
    (@eq_sym (Hom C z a) (@comp_fapp0 C z a a (@comp_fapp0 C a b a l f) u) u
      (@eq_ap (Hom C a a) (Hom C z a) (λ j : τ (Hom C a a), @comp_fapp0 C z a a j u)
        (@comp_fapp0 C a b a l f) (@id C a) (@omega_equiv_along_left_law C a b f E)))
    (@eq_trans (Hom C z a) (@comp_fapp0 C z a a (@comp_fapp0 C a b a l f) u)
      (@comp_fapp0 C z a a (@comp_fapp0 C a b a l f) v) v
      (@eq_ap (Hom C z b) (Hom C z a) (λ j : τ (Hom C z b), @comp_fapp0 C z b a l j)
        (@comp_fapp0 C z a b f u) (@comp_fapp0 C z a b f v) p)
      (@eq_ap (Hom C a a) (Hom C z a) (λ j : τ (Hom C a a), @comp_fapp0 C z a a j v)
        (@comp_fapp0 C a b a l f) (@id C a) (@omega_equiv_along_left_law C a b f E)));

// Cancel f before maps out of its target, using the supplied right inverse law.
symbol omega_equiv_precomp_reflect_path [C : Cat] [a b : τ (Obj C)]
  (f : τ (Hom C a b)) (E : τ (@OmegaEquivAlong C a b f)) (z : τ (Obj C))
  (u v : τ (Hom C b z))
  (p : τ (@= (Hom C a z) (@comp_fapp0 C a b z u f) (@comp_fapp0 C a b z v f)))
  : τ (@= (Hom C b z) u v)
≔ let r : τ (Hom C b a) ≔ @omega_equiv_along_right_inv C a b f E in
  @eq_trans (Hom C b z) u (@comp_fapp0 C b b z u (@comp_fapp0 C b a b f r)) v
    (@eq_sym (Hom C b z) (@comp_fapp0 C b b z u (@comp_fapp0 C b a b f r)) u
      (@eq_ap (Hom C b b) (Hom C b z) (λ j : τ (Hom C b b), @comp_fapp0 C b b z u j)
        (@comp_fapp0 C b a b f r) (@id C b) (@omega_equiv_along_right_law C a b f E)))
    (@eq_trans (Hom C b z) (@comp_fapp0 C b b z u (@comp_fapp0 C b a b f r))
      (@comp_fapp0 C b b z v (@comp_fapp0 C b a b f r)) v
      (@eq_ap (Hom C a z) (Hom C b z) (λ j : τ (Hom C a z), @comp_fapp0 C b a z j r)
        (@comp_fapp0 C a b z u f) (@comp_fapp0 C a b z v f) p)
      (@eq_ap (Hom C b b) (Hom C b z) (λ j : τ (Hom C b b), @comp_fapp0 C b b z v j)
        (@comp_fapp0 C b a b f r) (@id C b) (@omega_equiv_along_right_law C a b f E)));
