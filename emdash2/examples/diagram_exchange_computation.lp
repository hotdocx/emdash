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
