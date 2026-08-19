/* Reviewer for whole primitive/action-derived join-cross compatibility. */

require open emdash.emdash3_2_join_cross_compatibility;

// The higher-constructor beta is a whole path, not runtime conversion.
assert [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @join_map_extend_cross_beta A B C d
  : τ (@JoinCrossCompatibility A B C d);

assertnot [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @join_map_observe_cross
    A B C
    (@join_map_extend_object A B C d)
  ≡ @join_map_extend_cross A B C d;

// The path induces a directed whole displayed transformation.
assert [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @join_map_extend_cross_cell A B C d
  : τ (Hom
      (@JoinCross_cat A B C d)
      (@join_map_observe_cross
        A B C
        (@join_map_extend_object A B C d))
      (@join_map_extend_cross A B C d));

// A wrong target is rejected; the whole path has not collapsed its endpoints.
assertnot [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @join_map_extend_cross_cell A B C d
  : τ (Hom
      (@JoinCross_cat A B C d)
      (@join_map_observe_cross
        A B C
        (@join_map_extend_object A B C d))
      (@join_map_observe_cross
        A B C
        (@join_map_extend_object A B C d)));

// Endpoint components and arbitrary shaped equality are projections of the
// whole owner.
type λ A : Cat, λ B : Cat, λ C : Cat,
  λ d : τ (@JoinMapObjectData A B C),
  λ a : τ (Obj A), λ b : τ (Obj B),
    @join_map_extend_cross_component A B C d a b;

type λ A : Cat, λ B : Cat, λ C : Cat, λ I : Cat,
  λ d : τ (@JoinMapObjectData A B C),
  λ a : τ (Functor I A), λ b : τ (Functor I B),
    @join_map_extend_cross_shaped_beta A B C I d a b;

// The base-arrow action remains available one dimension higher.
type λ A : Cat, λ B : Cat, λ C : Cat,
  λ d : τ (@JoinMapObjectData A B C),
  λ ab : τ (Obj (Product_cat (Op_cat A) B)),
  λ ab' : τ (Obj (Product_cat (Op_cat A) B)),
  λ p : τ (Hom (Product_cat (Op_cat A) B) ab ab'),
  λ u : τ (Obj (Fibre_cat (@Terminal_prof A B) ab)),
    @tdapp1_int_cell
      (Product_cat (Op_cat A) B)
      (@Terminal_prof A B)
      (@join_map_target_prof A B C d)
      (@join_map_observe_cross
        A B C
        (@join_map_extend_object A B C d))
      (@join_map_extend_cross A B C d)
      (@join_map_extend_cross_cell A B C d)
      ab ab' p u;
