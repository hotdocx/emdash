/*
  Reviewer milestone: Grpd_cat function paths and explicit equivalence views.

  The hom-category between groupoid classifiers is the path category of
  ordinary functions. Category identity/composition keep their generic runtime
  owners, while stable pointwise function heads provide computation and meet
  them at proof time. Contractible-fibre `TypeEquiv` and equality-valued
  omega-equivalence are connected by explicit derived adapters; neither one is
  installed as groupoid-universe equality at this milestone.
*/

require open emdash.emdash3_2;

assert [A B : Grpd] ⊢
  Hom_cat Grpd_cat A B
  ≡ Path_cat (@Function_grpd A B);

assert [A : Grpd] ⊢
  @grpd_id_function A
  ≡ λ a : τ A, a;

// Typed reflexivity validates the proof-time identity comparison.
assert [A : Grpd] ⊢
  @eq_refl (@Function_grpd A A) (@id Grpd_cat A)
  : τ (@= (@Function_grpd A A)
      (@id Grpd_cat A)
      (@grpd_id_function A));

assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C) ⊢
  @grpd_comp_function A B C g f
  ≡ λ a : τ A, g (f a);

// Typed reflexivity validates the proof-time composition comparison.
assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C) ⊢
  @eq_refl (@Function_grpd A C)
    (@comp_fapp0 Grpd_cat A B C g f)
  : τ (@= (@Function_grpd A C)
      (@comp_fapp0 Grpd_cat A B C g f)
      (@grpd_comp_function A B C g f));

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_to_EQ1 Grpd_cat A B
    (@type_equiv_to_omega_EQ1 A B e)
  ≡ @type_equiv_to A B e;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_along_left_inv_EQ1
    Grpd_cat A B (@type_equiv_to A B e)
    (@omega_equiv_evidence_EQ1 Grpd_cat A B
      (@type_equiv_to_omega_EQ1 A B e))
  ≡ λ b : τ B, @type_equiv_from A B e b;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_equiv_along_left_law_EQ1
    Grpd_cat A B (@type_equiv_to A B e)
    (@omega_equiv_evidence_EQ1 Grpd_cat A B
      (@type_equiv_to_omega_EQ1 A B e))
  ≡ @type_equiv_omega_left_law_EQ1 A B e;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong_EQ1 Grpd_cat A B f)) ⊢
  @type_equiv_to A B
    (@omega_along_to_type_equiv_EQ1 A B f u)
  ≡ f;

// The reverse adapter selects the explicit left inverse as its fibre centre.
assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong_EQ1 Grpd_cat A B f))
  (b : τ B) ⊢
  @type_equiv_from A B
    (@omega_along_to_type_equiv_EQ1 A B f u)
    b
  ≡ (@omega_equiv_along_left_inv_EQ1 Grpd_cat A B f u) b;

assert [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong_EQ1 Grpd_cat A B f))
  (b : τ B) ⊢
  @type_equiv_right A B
    (@omega_along_to_type_equiv_EQ1 A B f u)
    b
  ≡ @omega_grpd_left_right_point_EQ1 A B f u b;

assert [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_to A B
    (@omega_to_type_equiv_EQ1 A B
      (@type_equiv_to_omega_EQ1 A B e))
  ≡ @type_equiv_to A B e;

// Identity retains its generic owner; capped composition is eta-observable.
assertnot [A : Grpd] ⊢
  @id Grpd_cat A
  ≡ λ a : τ A, a;

assert [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C) ⊢
  @comp_fapp0 Grpd_cat A B C g f
  ≡ λ a : τ A, g (f a);

// Direct groupoid-universe equality now has the stable EQ1 runtime form.
assert [A B : Grpd] ⊢
  @= Grpd_grpd A B
  ≡ @OmegaEquiv_EQ1 Grpd_cat A B;

// The adapters expose computational fields, not definitional package eta.
assertnot [A B : Grpd] (e : τ (TypeEquiv A B)) ⊢
  @omega_to_type_equiv_EQ1 A B
    (@type_equiv_to_omega_EQ1 A B e)
  ≡ e;

// The fibre contraction still comes from the pre-existing theorem capability.
assertnot [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (u : τ (@OmegaEquivAlong_EQ1 Grpd_cat A B f))
  (b : τ B) ⊢
  (sigma_Snd (@omega_grpd_is_equiv_EQ1 A B f u b))
    (sigma_Fst (@omega_grpd_is_equiv_EQ1 A B f u b))
  ≡ @eq_refl
      (@HFiber A B f b)
      (sigma_Fst (@omega_grpd_is_equiv_EQ1 A B f u b));
