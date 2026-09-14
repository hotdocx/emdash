require open emdash.emdash3_2_eq1_evidence_property;
require open emdash.emdash3_2_iso_evidence_constructors;

// Reuse the same fixed forward arrow and selected left inverse in IsoEvidence.
symbol omega_equiv_along_iso_evidence [C : Cat] [x y : τ (Obj C)]
  (f : τ (Hom C x y)) (E : τ (@OmegaEquivAlong C x y f)) : τ (IsoEvidence C x y)
≔ @iso_evidence_intro C x y f (@omega_equiv_along_left_inv C x y f E)
    (@omega_equiv_along_left_law C x y f E) (@omega_equiv_left_as_right_law C x y f E);

// Existing whole isomorphism composition supplies the fixed-forward composite evidence.
symbol omega_equiv_along_comp [C : Cat] [x y z : τ (Obj C)]
  (f : τ (Hom C x y)) (g : τ (Hom C y z))
  (E : τ (@OmegaEquivAlong C x y f)) (F : τ (@OmegaEquivAlong C y z g))
  : τ (@OmegaEquivAlong C x z (@comp_fapp0 C x y z g f))
≔ @iso_evidence_omega_along C x z (@iso_evidence_comp C x y z
    (@omega_equiv_along_iso_evidence C y z g F)
    (@omega_equiv_along_iso_evidence C x y f E));

// For an equal whole forward arrow, keep the same inverse and derive its two laws.
symbol omega_equiv_along_equal [C : Cat] [x y : τ (Obj C)]
  (f g : τ (Hom C x y)) (E : τ (@OmegaEquivAlong C x y f))
  (p : τ (@= (Hom C x y) f g)) : τ (@OmegaEquivAlong C x y g)
≔ @omega_equiv_along_intro C x y g
    (@omega_equiv_along_left_inv C x y f E) (@omega_equiv_along_left_inv C x y f E)
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C x y) (Hom C x x)
        (λ a : τ (Hom C x y), @comp_fapp0 C x y x (@omega_equiv_along_left_inv C x y f E) a)
        g f (@eq_sym _ _ _ p))
      (@omega_equiv_along_left_law C x y f E))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C x y) (Hom C y y)
        (λ a : τ (Hom C x y), @comp_fapp0 C y x y a (@omega_equiv_along_left_inv C x y f E))
        g f (@eq_sym _ _ _ p))
      (@omega_equiv_left_as_right_law C x y f E));
