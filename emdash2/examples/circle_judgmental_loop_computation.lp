/*
  Focused reviewer for judgmental Circle higher-constructor computation.

  The canonical dependent action of circle_ind on circle_loop reduces to its
  supplied PathOver datum. Constant-family circle_rec inherits that dependent
  computation. Ordinary eq_ap remains the separate J-derived observer and is
  intentionally only propositionally compared by circle_rec_beta_loop_path.
*/

require open emdash.emdash3_2_circle_hit;

// The stable generic owner retains its original J semantics propositionally.
assert [A : Grpd]
  [P : τ A → Grpd]
  (f : Π x : τ A, τ (P x))
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @eq_apd_ind_eqr_path A P f x y p
  : τ (@=
      (@PathOver A P x y p (f x) (f y))
      (@eq_apd A P f x y p)
      (@ind_eqr
        A y
        (λ x0 : τ A, λ p0 : τ (@= A x0 y),
          @PathOver A P x0 y p0 (f x0) (f y))
        (@eq_refl (P y) (f y))
        x p));

// The dependent Circle constructor beta is literal runtime computation.
assert (D : τ Circle_grpd → Grpd)
  (b : τ (D circle_base))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b)) ⊢
  @eq_refl
    (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b)
    ell
  : τ (@=
      (@PathOver
        Circle_grpd D
        circle_base circle_base circle_loop b b)
      (@eq_apd
        Circle_grpd D
        (λ x : τ Circle_grpd, @circle_ind D b ell x)
        circle_base circle_base circle_loop)
      ell);

// The named theorem is now the transparent typed view of that reduction.
assert (D : τ Circle_grpd → Grpd)
  (b : τ (D circle_base))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b)) ⊢
  @circle_ind_beta_loop D b ell
  ≡ @eq_refl
      (@PathOver
        Circle_grpd D
        circle_base circle_base circle_loop b b)
      ell;

// The derived constant-family recursor inherits dependent computation.
assert [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b)) ⊢
  @eq_apd
    Circle_grpd
    (λ _ : τ Circle_grpd, B)
    (λ x : τ Circle_grpd, @circle_rec B b ell x)
    circle_base circle_base circle_loop
  ≡ @const_pathover
      Circle_grpd B
      circle_base circle_base b b circle_loop ell;

// An arbitrary dependent section does not acquire the Circle-induction beta.
assertnot (D : τ Circle_grpd → Grpd)
  (f : Π x : τ Circle_grpd, τ (D x))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop
      (f circle_base) (f circle_base))) ⊢
  @eq_apd
    Circle_grpd D f
    circle_base circle_base circle_loop
  ≡ ell;

/*
  Ordinary eq_ap is independently derived from ind_eq. Making it a stable
  generic owner breaks an existing half-adjoint definitional proof, while a
  Circle-only match would inspect the expanded const_pathover/J tree. Keep the
  safe propositional circle_rec_beta_loop_path boundary for now.
*/
assertnot [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b)) ⊢
  @eq_ap
    Circle_grpd B
    (λ x : τ Circle_grpd, @circle_rec B b ell x)
    circle_base circle_base circle_loop
  ≡ ell;
