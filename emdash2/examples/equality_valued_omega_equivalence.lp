/*
  Reviewer milestone: equality-valued fixed-arrow evidence and stable facade.

  A fixed arrow carries separate inverse choices and ordinary equality laws in
  the next hom-categories. The first-class facade is abstract record-like data
  with computational construction, observation, and elimination. Its
  transparent Sigma presentation is a comparison view, while an object path
  acquires observable equivalence structure through the explicitly constructed
  `object_path_equiv_EQ1` package. Literal path categories have a narrow
  proof-time classifier join and explicit `path_equiv_EQ1` package; no generic
  equality/equivalence classifier comparison is promoted at this milestone.
*/

require open emdash.emdash3_2;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_intro_EQ1 C x y f l r alpha beta
  : τ (@OmegaEquivAlong_EQ1 C x y f);

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (l r : τ (Hom C y x))
  (alpha : τ (@= (Hom C x x)
    (@comp_fapp0 C x y x l f) (@id C x)))
  (beta : τ (@= (Hom C y y)
    (@comp_fapp0 C y x y f r) (@id C y))) ⊢
  @omega_equiv_along_left_inv_EQ1 C x y f
    (@omega_equiv_along_intro_EQ1 C x y f l r alpha beta)
  ≡ l;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_to_EQ1 C x y
    (@omega_equiv_pack_EQ1 C x y f u)
  ≡ f;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_evidence_EQ1 C x y
    (@omega_equiv_pack_EQ1 C x y f u)
  ≡ u;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_ind_EQ1 C x y
    (λ _ : τ (@OmegaEquiv_EQ1 C x y), Unit_grpd)
    (λ g : τ (Hom C x y),
     λ _ : τ (@OmegaEquivAlong_EQ1 C x y g), tt)
    (@omega_equiv_pack_EQ1 C x y f u)
  ≡ tt;

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_eta_EQ1 C x y
    (@omega_equiv_pack_EQ1 C x y f u)
  ≡ @eq_refl
      (@OmegaEquiv_EQ1 C x y)
      (@omega_equiv_pack_EQ1 C x y f u);

assert [C : Cat] (x y : τ (Obj C)) (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_sigma_to_facade_EQ1 C x y
    (@omega_facade_to_sigma_EQ1 C x y
      (@omega_equiv_pack_EQ1 C x y f u))
  ≡ @omega_equiv_pack_EQ1 C x y f u;

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_to_EQ1 C x y
    (@object_path_equiv_EQ1 C x y p)
  ≡ @path_to_hom C x y p;

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_along_left_inv_EQ1
    C x y
    (@path_to_hom C x y p)
    (@object_path_equiv_along_EQ1 C x y p)
  ≡ @path_to_hom C y x (@path_sym (Obj C) x y p);

assert [C : Cat] (x y : τ (Obj C))
  (p : τ (@= (Obj C) x y)) ⊢
  @omega_equiv_along_left_law_EQ1
    C x y
    (@path_to_hom C x y p)
    (@object_path_equiv_along_EQ1 C x y p)
  ≡ @object_path_equiv_left_law_EQ1 C x y p;

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_to_EQ1 C x x
    (@object_path_equiv_EQ1 C x x (@eq_refl (Obj C) x))
  ≡ @id C x;

// A literal path is accepted at the facade type by the narrow shaped join.
assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  p : τ (@OmegaEquiv_EQ1 (Path_cat A) x y);

// Its explicit package, rather than the raw path, owns observer computation.
assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_to_EQ1 (Path_cat A) x y
    (@path_equiv_EQ1 A x y p)
  ≡ p;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_along_left_inv_EQ1
    (Path_cat A) x y p
    (@path_equiv_along_EQ1 A x y p)
  ≡ @path_sym A x y p;

assert [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_ind_EQ1
    (Path_cat A) x y
    (λ _ : τ (@OmegaEquiv_EQ1 (Path_cat A) x y), @= A x y)
    (λ f : τ (Hom (Path_cat A) x y),
     λ _ : τ (@OmegaEquivAlong_EQ1 (Path_cat A) x y f), f)
    (@path_equiv_EQ1 A x y p)
  ≡ p;

// Typed reflexivity validates the proof-time Core-inclusion comparison.
assert [A : Grpd] ⊢
  @eq_refl
    (Hom Cat_cat (Path_cat A) (Path_cat A))
    (@Core_incl_func (Path_cat A))
  : τ (@=
      (Hom Cat_cat (Path_cat A) (Path_cat A))
      (@Core_incl_func (Path_cat A))
      (@id Cat_cat (Path_cat A)));

assert [A : Grpd] ⊢
  @path_cat_is_groupoidal_EQ1 A
  : τ (@IsGroupoidalCat_EQ1 (Path_cat A));

assert [A : Grpd] ⊢
  @omega_equiv_along_left_inv_EQ1
    Cat_cat
    (Core_cat (Path_cat A))
    (Path_cat A)
    (Core_incl_func (Path_cat A))
    (@path_cat_is_groupoidal_EQ1 A)
  ≡ @id Cat_cat (Path_cat A);

// A silently accepted raw path still has no package projection beta.
assertnot [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @omega_equiv_to_EQ1 (Path_cat A) x y p
  ≡ p;

assertnot [A : Grpd] (x y : τ A)
  (p : τ (@= A x y)) ⊢
  @path_equiv_EQ1 A x y p
  ≡ p;

assertnot [A : Grpd] ⊢
  @Core_incl_func (Path_cat A)
  ≡ @id Cat_cat (Path_cat A);

// The stable facade remains distinct from its transparent Sigma view.
assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @OmegaEquiv_EQ1 C x y
  ≡ @OmegaEquivSigma_EQ1 C x y;

// Facade eta is propositional rather than a runtime package collapse.
assertnot [C : Cat] (x y : τ (Obj C))
  (e : τ (@OmegaEquiv_EQ1 C x y)) ⊢
  @omega_equiv_pack_EQ1
    C x y
    (@omega_equiv_to_EQ1 C x y e)
    (@omega_equiv_evidence_EQ1 C x y e)
  ≡ e;

// Equality and facade classifiers are not yet runtime-convertible.
assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @= (Obj C) x y
  ≡ @OmegaEquiv_EQ1 C x y;

// The new facade remains separate from D0 until the explicit bridge phase.
assertnot [C : Cat] (x y : τ (Obj C)) ⊢
  @OmegaEquiv_EQ1 C x y
  ≡ @OmegaEquiv_D0 C x y;
