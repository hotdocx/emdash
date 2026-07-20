/*
  Reviewer milestone: frozen Candidate-D0b variable-evidence hom action. This
  is one of seven permitted compatibility consumers.

  A fixed-arrow equivalence certificate for F : A -> B induces one for every
  full hom action F_1[x,y]. The selected inverse hom functors are not raw hom
  actions of F's inverse functors: recursive inverse-cell components repair
  their object endpoints first. Both returned higher cells remain packaged
  and observable at the next hom level.
*/

require open emdash.emdash3_2;
require open emdash.emdash3_2_legacy_compat;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_along_fapp1_D0 A B F u x y
  : τ (@OmegaEquivAlong_D0
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_fapp1_left_inv_D0 u x y
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_fapp1_right_inv_D0 u x y
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x : τ (Obj A)) ⊢
  omega_equiv_along_fapp1_right_source_D0 u x
  : τ (Hom A
      x
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F x)));

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_left_inv_D0
    (@omega_equiv_along_fapp1_D0 A B F u x y)
  ≡ omega_equiv_along_fapp1_left_inv_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_right_inv_D0
    (@omega_equiv_along_fapp1_D0 A B F u x y)
  ≡ omega_equiv_along_fapp1_right_inv_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_to_D0
    (omega_equiv_along_left_cell_D0
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ omega_equiv_along_fapp1_left_cell_to_D0 u x y;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_to_D0
    (omega_equiv_along_right_cell_D0
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ omega_equiv_along_fapp1_right_cell_to_D0 u x y;

// Raw inverse hom actions still land at L(Fx),L(Fy) or R(Fx),R(Fy).
assertnot [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @fapp1_func
    B A
    (omega_equiv_along_left_functor_D0 u)
    (@fapp0 A B F x)
    (@fapp0 A B F y)
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));

assertnot [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @fapp1_func
    B A
    (omega_equiv_along_right_functor_D0 u)
    (@fapp0 A B F x)
    (@fapp0 A B F y)
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y));
