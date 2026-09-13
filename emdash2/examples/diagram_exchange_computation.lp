/* Double-exchange projection orders and the opposite mixed-action join. */
require open emdash.emdash3_2;

// Both reduction orders of double exchange retain the original whole rungs.
assert (A B C : Cat) (H : τ (Functor A (Functor_cat B C)))
  ⊢ @sym_func B A C (@sym_func A B C H) ≡ H;

assert (A B C : Cat) (H : τ (Functor A (Functor_cat B C))) (a : τ (Obj A))
  ⊢ @sym_fapp0_func B A C (@sym_func A B C H) a
    ≡ @fapp0 A (Functor_cat B C) H a;

assert (A B C : Cat) (H : τ (Functor A (Functor_cat B C)))
  (a a' : τ (Obj A))
  ⊢ @sym_fapp1_func B A C (@sym_func A B C H) a a'
    ≡ @fapp1_func A (Functor_cat B C) H a a';

assert (A B C : Cat) (H : τ (Functor A (Functor_cat B C)))
  (a a' : τ (Obj A)) (p : τ (Hom A a a'))
  ⊢ @sym_tapp1_fapp0_transf B A C (@sym_func A B C H) a a' p
    ≡ @fapp1_fapp0 A (Functor_cat B C) H a a' p;

assert (A B C : Cat) (H : τ (Functor A (Functor_cat B C)))
  (a : τ (Obj A)) (b b' : τ (Obj B))
  ⊢ @sym_fapp0_fapp1_func B A C (@sym_func A B C H) a b b'
    ≡ @fapp1_func B C (@fapp0 A (Functor_cat B C) H a) b b';

// Opposite action, direct and after its whole-functor projection.
// Give the return type in the native B presentation before comparing two
// inferred polymorphic types with differently presented opposite endpoints.
symbol probe_op_capped [A B : Cat]
  [F G : τ (Functor A B)] (eta : τ (@Transf A B F G))
  [x y : τ (Obj A)] (p : τ (Hom A x y))
  : τ (Hom B (@fapp0 A B F x) (@fapp0 A B G y))
≔ @tapp1_fapp0 (Op_cat A) (Op_cat B) (@Op_func A B G) (@Op_func A B F)
    y x (@Op_transf A B F G eta) p;

assert (A B : Cat) (F G : τ (Functor A B)) (eta : τ (@Transf A B F G))
  (x y : τ (Obj A)) (p : τ (Hom A x y))
  ⊢ @probe_op_capped A B F G eta x y p
    ≡ @tapp1_fapp0 A B F G x y eta p;

assert (A B : Cat) (F G : τ (Functor A B)) (eta : τ (@Transf A B F G))
  (x y : τ (Obj A)) (p : τ (Hom A x y))
  ⊢ @fapp0 (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B G y))
      (@tapp1_func (Op_cat A) (Op_cat B) (@Op_func A B G) (@Op_func A B F)
        y x (@Op_transf A B F G eta)) p
    ≡ @tapp1_fapp0 A B F G x y eta p;


assertnot (A B C : Cat) (H other : τ (Functor A (Functor_cat B C)))
  ⊢ @sym_func B A C (@sym_func A B C H) ≡ other;

// Focused owner-position consumers for the double-exchange action ladder.
assert (A B C : Cat) (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (@Transf A (Functor_cat B C) H K))
  ⊢ @sym_func_func_transf B A C (@sym_func A B C H) (@sym_func A B C K)
      (@sym_func_func_transf A B C H K eta) ≡ eta;
assert (A B C : Cat) (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (@Transf A (Functor_cat B C) H K)) (a : τ (Obj A))
  ⊢ @sym_transf_tapp0_transf B A C (@sym_func A B C H) (@sym_func A B C K)
      (@sym_func_func_transf A B C H K eta) a
    ≡ @tapp0_fapp0 A (Functor_cat B C) H K a eta;
assert (A B C : Cat) (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (@Transf A (Functor_cat B C) H K)) (a a' : τ (Obj A))
  ⊢ @tapp1_func A (Functor_cat B C) H K a a'
      (@sym_func_func_transf B A C (@sym_func A B C H) (@sym_func A B C K)
        (@sym_func_func_transf A B C H K eta))
    ≡ @tapp1_func A (Functor_cat B C) H K a a' eta;

// Overlap: either cancellation order in three exchanges gives one exchange.
assert (A B C : Cat) (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (@Transf A (Functor_cat B C) H K)) ⊢ (@sym_func_func_transf A B C H K (@sym_func_func_transf B A C (@sym_func
    A B C H) (@sym_func A B C K) (@sym_func_func_transf A B C H K eta))) ≡ (@sym_func_func_transf A B C H K eta);
// The whole and preprojected component routes agree.
assert (A B C : Cat) (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (@Transf A (Functor_cat B C) H K)) (a : τ (Obj A))
  ⊢ @tapp0_fapp0 A (Functor_cat B C) H K a (@sym_func_func_transf B A C (@sym_func A B C H) (@sym_func A B C K)
    (@sym_func_func_transf A B C H K eta))
    ≡ @sym_transf_tapp0_transf B A C (@sym_func A B C H) (@sym_func A B C K) (@sym_func_func_transf A B C H K eta) a;
assertnot (A B C : Cat) (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (@Transf A (Functor_cat B C) H K)) (other : τ (@Transf A (Functor_cat B C) H K))
  ⊢ eq_refl (@sym_func_func_transf B A C (@sym_func A B C H) (@sym_func A B C K) (@sym_func_func_transf A B C H K eta))
    : τ (@= (@Transf A (Functor_cat B C) H K) (@sym_func_func_transf B A C (@sym_func A B C H) (@sym_func A B C K)
    (@sym_func_func_transf A B C H K eta)) other);
// Original whole Hom action is retained at its next projection too.
assert (A B C : Cat) (H K : τ (Functor A (Functor_cat B C)))
  (eta : τ (@Transf A (Functor_cat B C) H K)) (a a' : τ (Obj A)) (p q : τ (Hom A a a'))
  ⊢ @fapp1_func _ _ (@tapp1_func A (Functor_cat B C) H K a a' (@sym_func_func_transf B A C (@sym_func A B C H)
    (@sym_func A B C K) (@sym_func_func_transf A B C H K eta))) p q
    ≡ @fapp1_func _ _ (@tapp1_func A (Functor_cat B C) H K a a' eta) p q;
