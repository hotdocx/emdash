/*
  Reviewer for the Nat-indexed canonical ordinal dependent-simplex source.

  Raw intrinsic flag codes drive a join-lift stage. The one-flag clause is the
  generic identity-join comparison and every later flag applies the generic
  PathOut transformation lift. The canonical Nat recursion then steps the
  existing code at F[s] and stores epsilon[s] as the new outgoing arrow.
*/

require open emdash.emdash3_2_dependent_simplex_ordinal_recursive;

assert [n : τ Nat_grpd] ⊢
  @OrdinalDependentSimplexSource n
  ≡ @DependentSimplexObservation (@DirectedSimplex_cat n) n;

// The indexed stage recursion computes at one, two, and three stored flags.
assert [A : Cat] (x0 : τ (Obj A)) ⊢
  @ordinal_join_lift_stage_from_code
    A zero (@dependent_simplex_code1 A x0)
  ≡ @ordinal_join_lift_stage_one A x0;

assert [A : Cat]
  (x0 : τ (Obj A))
  (e01 : τ (Obj (@DependentSimplex1_cat A x0))) ⊢
  @ordinal_join_lift_stage_from_code
    A (succ zero) (@dependent_simplex_code2 A x0 e01)
  ≡ @ordinal_join_lift_stage_step
      A zero (@PathOut_cat A x0)
      (@ordinal_join_lift_stage_one A x0) e01;

assert [A : Cat]
  (x0 : τ (Obj A))
  (e01 : τ (Obj (@DependentSimplex1_cat A x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat A x0 e01))) ⊢
  @ordinal_join_lift_stage_from_code
    A (succ (succ zero))
    (@dependent_simplex_code3 A x0 e01 t012)
  ≡ @ordinal_join_lift_stage_step
      A (succ zero) (@DependentSimplex2_cat A x0 e01)
      (@ordinal_join_lift_stage_from_code
        A (succ zero) (@dependent_simplex_code2 A x0 e01))
      t012;

// Nat recursion exposes its base and structural successor computations.
type ordinal_dependent_simplex_source_zero_object_path;

type λ n : τ Nat_grpd,
  @ordinal_dependent_simplex_source_successor_path n;

assert ⊢ @ordinal_dependent_simplex_source_code zero
  ≡ @dependent_simplex_code_zero (@DirectedSimplex_cat zero);

// Selected source objects compute and elaborate through the checked finite
// dimensions without introducing fixed-dimension cases in the recursor.
type @ordinal_dependent_simplex_source_object zero;
type @ordinal_dependent_simplex_source_object (succ zero);
type @ordinal_dependent_simplex_source_object (succ (succ zero));
type @ordinal_dependent_simplex_source_object
  (succ (succ (succ zero)));
type @ordinal_dependent_simplex_source_object
  (succ (succ (succ (succ zero))));

// Mapping and nonempty-face observation are variable-dimensional.
type λ n : τ Nat_grpd, λ C : Cat,
  λ H : τ (Functor (@DirectedSimplex_cat n) C),
    @ordinal_dependent_simplex_observation n C H;

type λ p : τ Nat_grpd, λ n : τ Nat_grpd, λ C : Cat,
  λ H : τ (Functor (@DirectedSimplex_cat n) C),
  λ alpha : τ (@DependentSimplexFaceRef p n),
    @ordinal_dependent_simplex_face p n C H alpha;

// The canonical nonzero stage retains another whole hom action.
type λ n : τ Nat_grpd,
  λ u : τ (Obj (@dependent_simplex_code_decode_cat
    (@DirectedSimplex_cat (succ n)) (succ n)
    (@ordinal_dependent_simplex_source_code (succ n)))),
  λ v : τ (Obj (@dependent_simplex_code_decode_cat
    (@DirectedSimplex_cat (succ n)) (succ n)
    (@ordinal_dependent_simplex_source_code (succ n)))),
    @ordinal_dependent_simplex_lift_next_action n u v;

// A face code at the wrong ambient dimension is rejected intrinsically.
assertnot ⊢ simplex_edge_zero_one_code
  : τ (@DependentSimplexFaceRef
      (succ zero) (succ (succ (succ (succ zero)))));

// The successor cell is not collapsed to an arbitrary replacement.
assertnot [n : τ Nat_grpd]
  (replacement : τ (Hom
    (@ordinal_join_lift_stage_target_cat
      (@DirectedSimplex_cat (succ n)) (succ n)
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n)))
      (@ordinal_dependent_simplex_lift_stage n))
    (@fapp0
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n)))
      (@ordinal_join_lift_stage_target_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        (@ordinal_dependent_simplex_lift_stage n))
      (@ordinal_join_lift_stage_left
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        (@ordinal_dependent_simplex_lift_stage n))
      (@ordinal_dependent_simplex_source_object (succ n)))
    (@fapp0
      (@dependent_simplex_code_decode_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@ordinal_dependent_simplex_source_code (succ n)))
      (@ordinal_join_lift_stage_target_cat
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        (@ordinal_dependent_simplex_lift_stage n))
      (@ordinal_join_lift_stage_right
        (@DirectedSimplex_cat (succ n)) (succ n)
        (@dependent_simplex_code_decode_cat
          (@DirectedSimplex_cat (succ n)) (succ n)
          (@ordinal_dependent_simplex_source_code (succ n)))
        (@ordinal_dependent_simplex_lift_stage n))
      (@ordinal_dependent_simplex_source_object (succ n))))) ⊢
  @ordinal_dependent_simplex_successor_cell n ≡ replacement;
