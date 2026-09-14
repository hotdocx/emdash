require open emdash.emdash3_2_omega_equiv_composition;

// Forward and inverse projections retain the original choices.
assert [C : Cat] [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z)) (E : τ (@OmegaEquivAlong C x y f)) (F
  : τ (@OmegaEquivAlong C y z g)) ⊢ @iso_evidence_to C x y (@omega_equiv_along_iso_evidence C x y f E) ≡ f;
assert [C : Cat] [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z)) (E : τ (@OmegaEquivAlong C x y f)) (F
  : τ (@OmegaEquivAlong C y z g)) ⊢ @iso_evidence_from C x y (@omega_equiv_along_iso_evidence C x y f E) ≡
  @omega_equiv_along_left_inv C x y f E;
assert [C : Cat] [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z)) (E : τ (@OmegaEquivAlong C x y f)) (F
  : τ (@OmegaEquivAlong C y z g)) ⊢ @omega_equiv_along_left_inv C x z (@comp_fapp0 C x y z g f)
  (@omega_equiv_along_comp C x y z f g E F) ≡ @comp_fapp0 C z y x (@omega_equiv_along_left_inv C x y f E)
  (@omega_equiv_along_left_inv C y z g F);
assert [C : Cat] [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z)) (E : τ (@OmegaEquivAlong C x y f)) (F
  : τ (@OmegaEquivAlong C y z g)) (f0 : τ (Hom C x y)) (p : τ (@= (Hom C x y) f f0)) ⊢ @omega_equiv_along_left_inv
  C x y f0 (@omega_equiv_along_equal C x y f f0 E p) ≡ @omega_equiv_along_left_inv C x y f E;
assertnot [C : Cat] [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z)) (E : τ (@OmegaEquivAlong C x y f))
  (F : τ (@OmegaEquivAlong C y z g)) (h : τ (Hom C x z)) ⊢ (@omega_equiv_along_comp C x y z f g E F) : τ
  (@OmegaEquivAlong C x z h);
assertnot [C : Cat] [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z)) (E : τ (@OmegaEquivAlong C x y f))
  (F : τ (@OmegaEquivAlong C y z g)) (g0 : τ (Hom C y z)) ⊢ @eq_refl (Hom C x z) (@comp_fapp0 C x y z g f) : τ (@=
  (Hom C x z) (@comp_fapp0 C x y z g f) (@comp_fapp0 C x y z g0 f));
