/*
  Focused reviewer for join-built ordinary simplex shapes.

  The whole join map reindexes the target's existing natural cross cell.
  Selected strict packages realize the two vertices of Delta[1] and the three
  edges of Delta[2]; their code-level and functor-level coface equations agree.
  The augmented empty face and arbitrary-code realization remain deferred.
*/

require open emdash.emdash3_2_simplex_shapes;

// Ordinary dimension n means n+1 vertices.
assert ⊢
  @DirectedSimplex_cat zero
  ≡ Terminal_cat;

assert ⊢
  @DirectedSimplex_cat (succ zero)
  ≡ WalkingArrow_cat;

assert ⊢
  @DirectedSimplex_cat (succ (succ zero))
  ≡ @Join_cat WalkingArrow_cat Terminal_cat;

// The generic join map restricts to its two supplied branch maps.
assert
  [A B A2 B2 : Cat]
  (F : τ (Functor A A2))
  (G : τ (Functor B B2)) ⊢
  @comp_fapp0
    Cat_cat A (@Join_cat A B) (@Join_cat A2 B2)
    (@join_map_func A B A2 B2 F G)
    (@join_fst_func A B)
  ≡ @join_map_left_func A B A2 B2 F;

assert
  [A B A2 B2 : Cat]
  (F : τ (Functor A A2))
  (G : τ (Functor B B2)) ⊢
  @comp_fapp0
    Cat_cat B (@Join_cat A B) (@Join_cat A2 B2)
    (@join_map_func A B A2 B2 F G)
    (@join_snd_func A B)
  ≡ @join_map_right_func A B A2 B2 G;

// Its cross datum remains one whole internally natural profunctor cell.
assert
  [A B A2 B2 : Cat]
  (F : τ (Functor A A2))
  (G : τ (Functor B B2)) ⊢
  @join_map_cross_transf A B A2 B2 F G
  : τ (Obj
      (@Prof_transf_cat
        (@Join_cat A2 B2)
        A
        (@Join_cat A2 B2)
        B
        (@Terminal_prof A B)
        (@join_map_left_func A B A2 B2 F)
        (@Unit_prof (@Join_cat A2 B2))
        (@join_map_right_func A B A2 B2 G)));

// Selected dictionaries project their face code and strict package carrier.
assert ⊢
  simplex_vertex_zero_code
  ≡ @face_skip
      (succ zero) (succ zero)
      (@face_identity (succ zero));

assert ⊢
  simplex_vertex_one_code
  ≡ @face_keep
      zero (succ zero)
      (@face_skip zero zero face_nil);

assert ⊢
  @strict_functor_underlying
    Terminal_cat WalkingArrow_cat
    (@selected_face_data
      zero (succ zero) simplex_vertex_zero_realization)
≡ @join_fst_func Terminal_cat Terminal_cat;

assert ⊢
  @strict_functor_underlying
    Terminal_cat WalkingArrow_cat
    (@selected_face_data
      zero (succ zero) simplex_vertex_one_realization)
≡ @join_snd_func Terminal_cat Terminal_cat;

assert ⊢
  @strict_functor_underlying
    WalkingArrow_cat
    (@Join_cat WalkingArrow_cat Terminal_cat)
    (@selected_face_data
      (succ zero) (succ (succ zero))
      simplex_edge_zero_one_realization)
≡ @join_fst_func WalkingArrow_cat Terminal_cat;

assert ⊢
  @strict_functor_underlying
    WalkingArrow_cat
    (@Join_cat WalkingArrow_cat Terminal_cat)
    (@selected_face_data
      (succ zero) (succ (succ zero))
      simplex_edge_zero_two_realization)
≡ @join_map_func
      Terminal_cat Terminal_cat WalkingArrow_cat Terminal_cat
      simplex_vertex_zero_func
      (@id_func Terminal_cat);

assert ⊢
  @strict_functor_underlying
    WalkingArrow_cat
    (@Join_cat WalkingArrow_cat Terminal_cat)
    (@selected_face_data
      (succ zero) (succ (succ zero))
      simplex_edge_one_two_realization)
≡ @join_map_func
      Terminal_cat Terminal_cat WalkingArrow_cat Terminal_cat
      simplex_vertex_one_func
      (@id_func Terminal_cat);

// Every selected realization retains semantic strictness evidence over the
// intrinsic compositor of its packaged carrier.
assert
  (p n : τ Nat_grpd)
  (R : τ (@SelectedFaceRealization p n)) ⊢
  @strict_functor_evidence
    (@DirectedSimplex_cat p)
    (@DirectedSimplex_cat n)
    (@selected_face_data p n R)
  : τ (@IsStrictFunctor
      (@DirectedSimplex_cat p)
      (@DirectedSimplex_cat n)
      (@strict_functor_underlying
        (@DirectedSimplex_cat p)
        (@DirectedSimplex_cat n)
        (@selected_face_data p n R)));

// Code-level first coface equation in the augmented index category.
assert ⊢
  @comp_fapp0
    SemiDeltaPlus_cat
    (succ zero)
    (succ (succ zero))
    (succ (succ (succ zero)))
    simplex_edge_zero_one_code
    simplex_vertex_zero_code
  ≡ @comp_fapp0
      SemiDeltaPlus_cat
      (succ zero)
      (succ (succ zero))
      (succ (succ (succ zero)))
      simplex_edge_zero_two_code
      simplex_vertex_zero_code;

// The same first coface equation holds between the realized whole functors.
assert ⊢
  @comp_fapp0
    Cat_cat
    (@DirectedSimplex_cat zero)
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    simplex_edge_zero_one_func
    simplex_vertex_zero_func
  ≡ @comp_fapp0
      Cat_cat
      (@DirectedSimplex_cat zero)
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_zero_two_func
      simplex_vertex_zero_func;

// The remaining two functorial coface equations use the other join branches.
assert ⊢
  @comp_fapp0
    Cat_cat
    (@DirectedSimplex_cat zero)
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    simplex_edge_zero_one_func
    simplex_vertex_one_func
  ≡ @comp_fapp0
      Cat_cat
      (@DirectedSimplex_cat zero)
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_one_two_func
      simplex_vertex_zero_func;

assert ⊢
  @comp_fapp0
    Cat_cat
    (@DirectedSimplex_cat zero)
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    simplex_edge_zero_two_func
    simplex_vertex_one_func
  ≡ @comp_fapp0
      Cat_cat
      (@DirectedSimplex_cat zero)
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      simplex_edge_one_two_func
      simplex_vertex_one_func;

// Vertex-count codes are not silently reinterpreted as augmented empty faces.
assertnot ⊢
  simplex_vertex_zero_code
  : τ (@FaceCode zero (succ zero));
