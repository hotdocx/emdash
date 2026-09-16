/* Both transported inverse slots retain the computed m∘f⁻¹. */
require open emdash.emdash3_2_omega_equiv_right_factor;

assert [C : Cat] [A B D : τ (Obj C)]
 (m : τ (Hom C A B)) (f : τ (Hom C A D)) (g : τ (Hom C B D))
 (M : τ (@OmegaEquivAlong C A B m)) (F : τ (@OmegaEquivAlong C A D f))
 (p : τ (@= (Hom C A D) (@comp_fapp0 C A B D g m) f))
 ⊢ (@omega_equiv_along_left_inv C B D g (@omega_equiv_right_factor C A B D m f g M F p))
  ≡ (@comp_fapp0 C D A B m (@omega_equiv_along_left_inv C A D f F));

assert [C : Cat] [A B D : τ (Obj C)]
 (m : τ (Hom C A B)) (f : τ (Hom C A D)) (g : τ (Hom C B D))
 (M : τ (@OmegaEquivAlong C A B m)) (F : τ (@OmegaEquivAlong C A D f))
 (p : τ (@= (Hom C A D) (@comp_fapp0 C A B D g m) f))
 ⊢ (@omega_equiv_along_right_inv C B D g (@omega_equiv_right_factor C A B D m f g M F p))
  ≡ (@comp_fapp0 C D A B m (@omega_equiv_along_left_inv C A D f F));
