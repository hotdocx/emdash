/*
  Reviewer for the first-stage join mapping observation/extension interface.

  The two restrictions are whole functors and retain their hom action.  The
  cross observation is derived from the existing profunctor action and remains
  internally natural in both join endpoints.  Object-level extension computes
  on both branches and at the primitive cross owner.  Broad eta and the
  comparison with the action-derived cross are intentionally absent.
*/

require open emdash.emdash3_2_join_mapping_recursion;

// Whole branch restrictions retain generic transfor action.
assert [A B C : Cat]
  (H K : τ (Functor (@Join_cat A B) C)) ⊢
  @fapp1_func
    (@Functor_cat (@Join_cat A B) C)
    (@Functor_cat A C)
    (@join_map_observe_left_func A B C)
    H K
  : τ (Functor
      (@Transf_cat (@Join_cat A B) C H K)
      (@Transf_cat A C
        (@fapp0
          (@Functor_cat (@Join_cat A B) C)
          (@Functor_cat A C)
          (@join_map_observe_left_func A B C) H)
        (@fapp0
          (@Functor_cat (@Join_cat A B) C)
          (@Functor_cat A C)
          (@join_map_observe_left_func A B C) K)));

assert [A B C : Cat]
  (H K : τ (Functor (@Join_cat A B) C)) ⊢
  @fapp1_func
    (@Functor_cat (@Join_cat A B) C)
    (@Functor_cat B C)
    (@join_map_observe_right_func A B C)
    H K
  : τ (Functor
      (@Transf_cat (@Join_cat A B) C H K)
      (@Transf_cat B C
        (@fapp0
          (@Functor_cat (@Join_cat A B) C)
          (@Functor_cat B C)
          (@join_map_observe_right_func A B C) H)
        (@fapp0
          (@Functor_cat (@Join_cat A B) C)
          (@Functor_cat B C)
          (@join_map_observe_right_func A B C) K)));

// The whole branch owners have explicit proof-time comparisons with the
// readable direct precomposition aliases.
assert [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C)) ⊢
  @join_map_observe_left_path A B C H
  : τ (@=
      (Obj (@Functor_cat A C))
      (@fapp0
        (@Functor_cat (@Join_cat A B) C)
        (@Functor_cat A C)
        (@join_map_observe_left_func A B C) H)
      (@join_map_observe_left A B C H));

assert [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C)) ⊢
  @join_map_observe_right_path A B C H
  : τ (@=
      (Obj (@Functor_cat B C))
      (@fapp0
        (@Functor_cat (@Join_cat A B) C)
        (@Functor_cat B C)
        (@join_map_observe_right_func A B C) H)
      (@join_map_observe_right A B C H));

// The generic cross observation is whole, and shaped evaluation is available.
assert [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C)) ⊢
  @join_map_observe_cross A B C H
  : τ (Obj
      (@Prof_transf_cat
        C A C B
        (@Terminal_prof A B)
        (@join_map_observe_left A B C H)
        (@Unit_prof C)
        (@join_map_observe_right A B C H)));

assert [A B C I : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  (a : τ (Functor I A))
  (b : τ (Functor I B)) ⊢
  @join_map_observe_cross_at A B C I H a b
  : τ (@Prof_hom
      I C C
      (@comp_cat_fapp0
        I A C
        (@join_map_observe_left A B C H) a)
      (@Unit_prof C)
      (@comp_cat_fapp0
        I B C
        (@join_map_observe_right A B C H) b));

// Object-data projections compute on observation.
assert [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C)) ⊢
  @join_map_object_left A B C
    (@join_map_observe_object A B C H)
  ≡ @join_map_observe_left A B C H;

assert [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C)) ⊢
  @join_map_object_right A B C
    (@join_map_observe_object A B C H)
  ≡ @join_map_observe_right A B C H;

assert [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C)) ⊢
  @join_map_object_cross A B C
    (@join_map_observe_object A B C H)
  ≡ @join_map_observe_cross A B C H;

// Extension computes on both join branches.
assert [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @comp_fapp0
    Cat_cat A (@Join_cat A B) C
    (@join_map_extend_object A B C d)
    (@join_fst_func A B)
  ≡ @join_map_object_left A B C d;

assert [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @comp_fapp0
    Cat_cat B (@Join_cat A B) C
    (@join_map_extend_object A B C d)
    (@join_snd_func A B)
  ≡ @join_map_object_right A B C d;

// The primitive cross owner computes to the supplied cross datum.
assert [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @join_map_extend_cross A B C d
  ≡ @join_map_object_cross A B C d;

// The action-derived cross is not silently identified with that primitive
// observation, and the kernel has no broad join eta.
assertnot [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C)) ⊢
  @join_map_observe_cross A B C
    (@join_map_extend_object A B C d)
  ≡ @join_map_object_cross A B C d;

assertnot [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C)) ⊢
  @join_map_extend_object A B C
    (@join_map_observe_object A B C H)
  ≡ H;
