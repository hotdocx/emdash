/*
  Reviewer surface for the represented Path associator.

  The generic represented compositor remains whole and directed.  Its Path
  specialization is an invertible equality with readable bracketings, while
  its proof term remains distinct from the direct J associator.
*/

require open emdash.emdash3_2_dependent_simplex_path_associator;

// Direct J associativity computes when the first path is reflexive.
assert [A : Grpd]
  [x y z : τ A]
  (g : τ (@= A x y))
  (h : τ (@= A y z)) ⊢
  @path_cat_assoc_J A x x (@eq_refl A x) y g z h
  ≡ @eq_refl
      (@= A x z)
      (@comp_fapp0 (Path_cat A) x y z h g);

// The whole source is exactly the generic represented compositor endpoint.
assert [Z : Cat]
  [x0 x1 x2 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2)) ⊢
  @represented_assoc_transfd Z x0 x1 x2 f g
  ≡ @fapp1_compositor
      (Op_cat Z)
      (@Catd_cat Z)
      (@Rep_catd_func Z)
      x2 x1 x0 f g;

// Its point projection is a directed cell between retained formal endpoints.
assert [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3)) ⊢
  @represented_assoc_cell Z x0 x1 x2 x3 f g h
  : τ (Hom
      (Hom_cat Z x0 x3)
      (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
      (@represented_assoc_rhs Z x0 x1 x2 x3 f g h));

// Both Path endpoint comparisons have the expected readable bracketings.
assert [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z)) ⊢
  @path_represented_assoc_lhs_agrees A w x f y g z h
  : τ (@=
      (@= A w z)
      (@represented_assoc_lhs (Path_cat A) w x y z f g h)
      (@comp_fapp0
        (Path_cat A) w x z
        (@comp_fapp0 (Path_cat A) x y z h g)
        f));

assert [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z)) ⊢
  @path_represented_assoc_rhs_agrees A w x f y g z h
  : τ (@=
      (@= A w z)
      (@represented_assoc_rhs (Path_cat A) w x y z f g h)
      (@comp_fapp0
        (Path_cat A) w y z h
        (@comp_fapp0 (Path_cat A) w x y g f)));

// The represented cell yields the forward groupoidal associator.
assert [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z)) ⊢
  @path_represented_assoc A w x f y g z h
  : τ (@=
      (@= A w z)
      (@comp_fapp0
        (Path_cat A) w x z
        (@comp_fapp0 (Path_cat A) x y z h g)
        f)
      (@comp_fapp0
        (Path_cat A) w y z h
        (@comp_fapp0 (Path_cat A) w x y g f)));

// Equality symmetry supplies the inverse without a new inverse record.
type λ A : Grpd,
  λ w : τ A, λ x : τ A, λ f : τ (@= A w x),
  λ y : τ A, λ g : τ (@= A x y),
  λ z : τ A, λ h : τ (@= A y z),
    @eq_sym _ _ _ (@path_represented_assoc A w x f y g z h);

// Same endpoints do not imply definitional equality of coherence provenance.
assertnot [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z)) ⊢
  @path_represented_assoc A w x f y g z h
  ≡ @path_assoc_J_forward A w x f y g z h;

// A separately indexed final arrow is rejected by the retained endpoint.
assertnot [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h h' : τ (Hom Z x2 x3)) ⊢
  @represented_assoc_cell Z x0 x1 x2 x3 f g h
  : τ (Hom
      (Hom_cat Z x0 x3)
      (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
      (@represented_assoc_rhs Z x0 x1 x2 x3 f g h'));

// The next action remains a whole functor and can be iterated again.
type λ Z : Cat,
  λ x0 : τ (Obj Z), λ x1 : τ (Obj Z),
  λ x2 : τ (Obj Z),
  λ f : τ (Hom Z x0 x1),
  λ g : τ (Hom Z x1 x2),
  λ x3 : τ (Obj Z),
  λ h0 : τ (Hom Z x2 x3),
  λ h1 : τ (Hom Z x2 x3),
    @fapp1_func
      _ _
      (@represented_assoc_higher_func Z x0 x1 x2 f g x3 h0 h1);
