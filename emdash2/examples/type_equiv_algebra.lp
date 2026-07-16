/*
  Reviewer milestone: ordinary algebra of contractible-fibre type equivalences.

  Identity, symmetry, and categorical-order composition carry explicit
  IsEquivMap evidence. Transparent packages expose their forward maps and the
  selected inverse/right path, while no package-level eta or inverse-law
  cancellation is installed as runtime computation.
*/

require open emdash.emdash3_2;

assert [A : Grpd] ⊢
  @type_equiv_refl_is_equiv A
  : τ (@IsEquivMap A A (λ x : τ A, x));

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B) ⊢
  type_equiv_to (@type_equiv_sym A B e) b
  ≡ type_equiv_from e b;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_from (@type_equiv_sym A B e) a
  ≡ type_equiv_to e a;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_right (@type_equiv_sym A B e) a
  ≡ type_equiv_left e a;

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to (@type_equiv_comp A B C eBC eAB) a
  ≡ type_equiv_to eBC (type_equiv_to eAB a);

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (c : τ C) ⊢
  type_equiv_from (@type_equiv_comp A B C eBC eAB) c
  ≡ type_equiv_from eAB (type_equiv_from eBC c);

assert [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (c : τ C) ⊢
  type_equiv_right (@type_equiv_comp A B C eBC eAB) c
  ≡ @type_equiv_comp_right A B C eBC eAB c;

assert [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to
    (@type_equiv_comp A B B (@type_equiv_refl B) e)
    a
  ≡ type_equiv_to e a;

assert [A B C D : Grpd]
  (eCD : τ (TypeEquiv C D))
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A) ⊢
  type_equiv_to
    (@type_equiv_comp A C D eCD
      (@type_equiv_comp A B C eBC eAB))
    a
  ≡ type_equiv_to
      (@type_equiv_comp A B D
        (@type_equiv_comp B C D eCD eBC)
        eAB)
      a;

assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_sym B A (@type_equiv_sym A B e)
  ≡ e;

assertnot [A B : Grpd]
  (e : τ (TypeEquiv A B)) ⊢
  @type_equiv_comp A B B (@type_equiv_refl B) e
  ≡ e;
