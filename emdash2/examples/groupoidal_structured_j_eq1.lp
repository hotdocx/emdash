/*
  Reviewer example: internal groupoidality and structured J.

  An EQ1 witness for Core(C) -> C acts on every hom through the existing D0b
  compatibility owner. Its selected inverse reads a directed arrow as an
  object path, and the equality-valued right law proves that re-inclusion
  recovers the arrow. Existing discrete and zero-dimensional categories are
  nonliteral consumers. The selected path also reconstructs explicit
  equivalence evidence for the arrow, so existing displayed transport is an
  equivalence of fibres. Structured motives continue to use `path_ind_sec`;
  no parallel groupoidal eliminator is introduced.
*/

require open emdash.emdash3_2;

// Internal groupoidality is iterable at the next hom dimension.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  (x y : τ (Obj C)) ⊢
  @groupoidal_core_homwise_EQ1 C g x y
  : τ (@OmegaEquivAlong_EQ1
      Cat_cat
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y));

// The selected inverse sends one directed arrow back to an object path.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_arrow_to_path_EQ1 C g x y f
  : τ (@= (Obj C) x y);

// Re-including that selected path is propositionally the original arrow.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_path_to_arrow_retract_EQ1 C g x y f
  : τ (@=
      (Hom C x y)
      (@fapp0
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (@core_incl_hom_func C x y)
        (@groupoidal_arrow_to_path_EQ1 C g x y f))
      f);

// The selected path and its reverse construct native equivalence evidence for
// the original arrow; this is a transparent derivation, not a decoder axiom.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_arrow_equiv_along_EQ1 C g x y f
  : τ (@OmegaEquivAlong_EQ1 C x y f);

assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @omega_equiv_along_left_inv_EQ1 C x y f
    (@groupoidal_arrow_equiv_along_EQ1 C g x y f)
  ≡ @groupoidal_arrow_inverse_EQ1 C g x y f;

// Existing displayed transport carries the corresponding fibre equivalence.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  (D : τ (Catd C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @groupoidal_fibre_transport_equiv_EQ1 C g D x y f
  : τ (@OmegaEquivAlong_EQ1
      Cat_cat
      (Fibre_cat D x)
      (Fibre_cat D y)
      (@fapp1_fapp0 C Cat_cat D x y f));

assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  (D : τ (Catd C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @omega_equiv_along_left_inv_EQ1
    Cat_cat
    (Fibre_cat D x)
    (Fibre_cat D y)
    (@fapp1_fapp0 C Cat_cat D x y f)
    (@groupoidal_fibre_transport_equiv_EQ1 C g D x y f)
  ≡ @fapp1_fapp0 C Cat_cat D y x
      (@groupoidal_arrow_inverse_EQ1 C g x y f);

// The earlier discrete-category contract supplies a general nonliteral case.
assert [C : Cat]
  (d : τ (IsDiscreteCat C)) ⊢
  @discrete_cat_is_groupoidal_EQ1 C d
  : τ (@IsGroupoidalCat_EQ1 C);

// A packaged zero-category is a concrete carrier whose head is not Path_cat.
assert (X : τ ZeroCat) ⊢
  @zero_cat_is_groupoidal_EQ1 X
  : τ (@IsGroupoidalCat_EQ1 (@ncat_carrier cat_zero X));

// The generic construction remains well typed at a literal path category.
assert [A : Grpd]
  [x y : τ A] ⊢
  @groupoidal_core_homwise_EQ1
    (Path_cat A)
    (@path_cat_is_groupoidal_EQ1 A)
    x
    y
  : τ (@OmegaEquivAlong_EQ1
      Cat_cat
      (Hom_cat (Core_cat (Path_cat A)) x y)
      (Hom_cat (Path_cat A) x y)
      (@fapp1_func
        (Core_cat (Path_cat A))
        (Path_cat A)
        (@Core_incl_func (Path_cat A))
        x
        y));

// Compatibility-derived inverse selection is not advertised as literal-path
// computation; the direct explicit package remains the computational owner.
assertnot [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @groupoidal_arrow_to_path_EQ1
    (Path_cat A)
    (@path_cat_is_groupoidal_EQ1 A)
    x
    y
    p
  ≡ p;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @omega_equiv_to_EQ1
    (Path_cat A)
    x
    y
    (@path_equiv_EQ1 A x y p)
  ≡ p;

// Structured groupoidal J is the existing directed-family action.
assert [C : Cat]
  (g : τ (@IsGroupoidalCat_EQ1 C))
  (D : τ (Catd C))
  (x : τ (Obj C))
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_ind_sec
    C
    x
    (@Sigma_proj1_pullback_catd C (@Rep_catd C x) D)
    u
  ≡ @fib_cov_transf C D x u;

/*
  At the literal source `Path_cat(A)`, the directed-family action and the
  primitive right-J eliminator are now compared by a derived theorem. The
  existing `path_ind_sec` application factors through the same structured
  action, so all three presentations agree propositionally.
*/
assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y)) ⊢
  @path_cat_structured_transport_agrees_ind_eqr_EQ1 A D x y u p
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_structured_transport_EQ1 A D x y u p)
      (@path_cat_ind_eqr_transport_EQ1 A D x y u p));

assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y)) ⊢
  @path_cat_path_ind_app_agrees_ind_eqr_EQ1 A D x y u p
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_path_ind_app_EQ1 A D x y u p)
      (@path_cat_ind_eqr_transport_EQ1 A D x y u p));

// Primitive J retains its ordinary reflexivity computation.
assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A)
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_cat_ind_eqr_transport_EQ1 A D x x u (@eq_refl A x)
  ≡ u;

/*
  The structured action intentionally keeps its directed runtime normal form.
  Its reflexive comparison with `u` is proof-time/propositional, rather than a
  second runtime reduction.
*/
assertnot [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A)
  (u : τ (Obj (Fibre_cat D x))) ⊢
  @path_cat_structured_transport_EQ1 A D x x u (@eq_refl A x)
  ≡ u;

// Typed reflexivity exercises the proof-time path-category identity join.
assert [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  (x : τ A) ⊢
  @eq_refl
    (Hom Cat_cat (Fibre_cat D x) (Fibre_cat D x))
    (@fapp1_fapp0
      (Path_cat A) Cat_cat D x x (@eq_refl A x))
  : τ (@=
      (Hom Cat_cat (Fibre_cat D x) (Fibre_cat D x))
      (@fapp1_fapp0
        (Path_cat A) Cat_cat D x x (@eq_refl A x))
      (@id Cat_cat (Fibre_cat D x)));
