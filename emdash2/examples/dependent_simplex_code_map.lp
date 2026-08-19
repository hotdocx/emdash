/* Reviewer for functorial mapped decoding of intrinsic simplex codes. */

require open emdash.emdash3_2_dependent_simplex_code_map;

// Zero maps to the target zero code and the supplied functor itself.
assert [C D : Cat] (F : τ (Functor C D)) ⊢
  @dependent_simplex_code_map_target
    C D F zero (@dependent_simplex_code_zero C)
  ≡ @dependent_simplex_code_zero D;

assert [C D : Cat] (F : τ (Functor C D)) ⊢
  @dependent_simplex_code_map_func
    C D F zero (@dependent_simplex_code_zero C)
  ≡ F;

// One successor maps its flag and returns the existing PathOut map.
assert [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C)) ⊢
  @dependent_simplex_code_map_target
    C D F (succ zero) (@dependent_simplex_code1 C x0)
  ≡ @dependent_simplex_code1 D (@fapp0 C D F x0);

assert [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C)) ⊢
  @dependent_simplex_code_map_func
    C D F (succ zero) (@dependent_simplex_code1 C x0)
  ≡ @dependent_simplex1_map C D F x0;

// Selected higher codes recover the already-promoted whole native maps.
assert [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0))) ⊢
  @dependent_simplex_code_map_func
    C D F (succ (succ zero))
    (@dependent_simplex_code2 C x0 e01)
  ≡ @dependent_simplex2_map C D F x0 e01;

assert [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012))) ⊢
  @dependent_simplex_code_map_func
    C D F (succ (succ (succ (succ zero))))
    (@dependent_simplex_code4 C x0 e01 t012 s0123)
  ≡ @dependent_simplex4_map C D F x0 e01 t012 s0123;

// Mapped decoding remains whole at another hom level.
type λ C : Cat, λ D : Cat, λ F : τ (Functor C D),
  λ x0 : τ (Obj C),
  λ e01 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)),
  λ s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)),
  λ w0 : τ (Obj (@DependentSimplex4_cat C x0 e01 t012 s0123)),
  λ w1 : τ (Obj (@DependentSimplex4_cat C x0 e01 t012 s0123)),
    @fapp1_func
      _ _
      (@dependent_simplex_code_map_func
        C D F (succ (succ (succ (succ zero))))
        (@dependent_simplex_code4 C x0 e01 t012 s0123))
      w0 w1;

// Endpoint views map both endpoints by the decoded functor.
assert [C D : Cat]
  (F : τ (Functor C D))
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (v : τ (@DependentSimplexEndpointView C n c)) ⊢
  sigma_Fst (@dependent_simplex_endpoint_view_map C D F n c v)
  ≡ @fapp0
      _ _
      (@dependent_simplex_code_map_func C D F n c)
      (sigma_Fst v);

assert [C D : Cat]
  (F : τ (Functor C D))
  [n : τ Nat_grpd]
  (c : τ (@DependentSimplexCode C n))
  (v : τ (@DependentSimplexEndpointView C n c)) ⊢
  sigma_Fst (sigma_Snd
    (@dependent_simplex_endpoint_view_map C D F n c v))
  ≡ @fapp0
      _ _
      (@dependent_simplex_code_map_func C D F n c)
      (sigma_Fst (sigma_Snd v));
