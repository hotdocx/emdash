/*
  Join-built ordinary simplex shapes and selected face realizations.

  `DirectedSimplex_cat(n)` is the ordinary n-simplex category with n+1
  vertices: it starts at Terminal_cat and joins one terminal vertex at each
  successor. This dimension convention is intentionally distinct from the
  augmented index category's vertex-count convention. A selected realization
  from dimension p to n therefore carries a FaceCode(succ p,succ n).

  The generic join map is assembled by join elimination. Its cross datum is
  the target join's existing whole cross cell reindexed along the two input
  functors, so no external naturality family is added. Selected strict codes
  close join inclusions and join maps under the active strict profile.

  This first slice realizes the two vertices of Delta[1] and the three edges
  of Delta[2]. It does not yet realize the augmented empty ordinal, arbitrary
  face codes, degeneracies, representables, boundaries, horns, or Kan data.
*/

require open emdash.emdash3_2_semisimplicial_index;
require open emdash.emdash3_2_walking_arrow;
require open emdash.emdash3_2_gray_profiles;

// Left branch of the bifunctorial join map.
symbol join_map_left_func
  [A B A2 B2 : Cat]
  (F : τ (Functor A A2))
  : τ (Functor A (@Join_cat A2 B2))
≔ @comp_cat_fapp0
    A A2 (@Join_cat A2 B2)
    (@join_fst_func A2 B2)
    F;

// Right branch of the bifunctorial join map.
symbol join_map_right_func
  [A B A2 B2 : Cat]
  (G : τ (Functor B B2))
  : τ (Functor B (@Join_cat A2 B2))
≔ @comp_cat_fapp0
    B B2 (@Join_cat A2 B2)
    (@join_snd_func A2 B2)
    G;

/*
  Whole internally natural cross datum. Constant-profunctor reindexing and
  nested-reindex accumulation compute its endpoints to the two branch maps.
*/
symbol join_map_cross_transf
  [A B A2 B2 : Cat]
  (F : τ (Functor A A2))
  (G : τ (Functor B B2))
  : τ (Obj
      (@Prof_transf_cat
        (@Join_cat A2 B2)
        A
        (@Join_cat A2 B2)
        B
        (@Terminal_prof A B)
        (@join_map_left_func A B A2 B2 F)
        (@Unit_prof (@Join_cat A2 B2))
        (@join_map_right_func A B A2 B2 G)))
≔ @Prof_reindex_transf
    A2 A B2 B
    (@Terminal_prof A2 B2)
    (@Prof_reindex
      (@Join_cat A2 B2) A2
      (@Join_cat A2 B2) B2
      (@Unit_prof (@Join_cat A2 B2))
      (@join_fst_func A2 B2)
      (@join_snd_func A2 B2))
    (@join_cross_transf A2 B2)
    F G;

// Bifunctorial action on join shapes, derived from the existing recursor.
symbol join_map_func
  [A B A2 B2 : Cat]
  (F : τ (Functor A A2))
  (G : τ (Functor B B2))
  : τ (Functor (@Join_cat A B) (@Join_cat A2 B2))
≔ @join_elim_func
    A B (@Join_cat A2 B2)
    (@join_map_left_func A B A2 B2 F)
    (@join_map_right_func A B A2 B2 G)
    (@join_map_cross_transf A B A2 B2 F G);

// Join inclusions preserve the selected strict-functor profile.
injective symbol strict_join_fst_data
  (A B : Cat)
  : τ (@StrictFunctorData A (@Join_cat A B));

rule @strict_functor_carrier _ _ (@strict_join_fst_data $A $B)
  ↪ @join_fst_func $A $B;

injective symbol strict_join_snd_data
  (A B : Cat)
  : τ (@StrictFunctorData B (@Join_cat A B));

rule @strict_functor_carrier _ _ (@strict_join_snd_data $A $B)
  ↪ @join_snd_func $A $B;

// Join maps of two selected strict codes remain selected strict codes.
injective symbol strict_join_map_data
  [A B A2 B2 : Cat]
  (F : τ (@StrictFunctorData A A2))
  (G : τ (@StrictFunctorData B B2))
  : τ (@StrictFunctorData
      (@Join_cat A B)
      (@Join_cat A2 B2));

rule @strict_functor_carrier _ _
      (@strict_join_map_data $A $B $A2 $B2 $F $G)
  ↪ @join_map_func
      $A $B $A2 $B2
      (@strict_functor_carrier $A $A2 $F)
      (@strict_functor_carrier $B $B2 $G);

// Ordinary n-simplex category: [0] = 1 and [n+1] = [n] star 1.
symbol DirectedSimplex_cat
  (n : τ Nat_grpd)
  : Cat
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj Cat_cat)
    Terminal_cat
    (λ _ : τ Nat_grpd,
      λ previous : τ (Obj Cat_cat),
      @Join_cat previous Terminal_cat)
    n;

/*
  A selected nonempty face realization pairs its vertex-count code with one
  strict-profile whole functor between the corresponding ordinary shapes.
  This is a bounded executable dictionary, not yet a decoder for every code.
*/
symbol SelectedFaceRealization
  (p n : τ Nat_grpd)
  : Grpd
≔ @Product_grpd
    (@FaceCode (succ p) (succ n))
    (@StrictFunctorData
      (@DirectedSimplex_cat p)
      (@DirectedSimplex_cat n));

symbol selected_face_code
  [p n : τ Nat_grpd]
  (R : τ (@SelectedFaceRealization p n))
  : τ (@FaceCode (succ p) (succ n))
≔ sigma_Fst R;

symbol selected_face_data
  [p n : τ Nat_grpd]
  (R : τ (@SelectedFaceRealization p n))
  : τ (@StrictFunctorData
      (@DirectedSimplex_cat p)
      (@DirectedSimplex_cat n))
≔ sigma_Snd R;

symbol selected_face_func
  [p n : τ Nat_grpd]
  (R : τ (@SelectedFaceRealization p n))
  : τ (Functor
      (@DirectedSimplex_cat p)
      (@DirectedSimplex_cat n))
≔ @strict_functor_carrier
    (@DirectedSimplex_cat p)
    (@DirectedSimplex_cat n)
    (@selected_face_data p n R);

// Vertex 0 of Delta[1].
symbol simplex_vertex_zero_realization
  : τ (@SelectedFaceRealization zero (succ zero))
≔ @Product_pair_grpd
    (@FaceCode (succ zero) (succ (succ zero)))
    (@StrictFunctorData Terminal_cat WalkingArrow_cat)
    (@face_skip
      (succ zero) (succ zero)
      (@face_identity (succ zero)))
    (@strict_join_fst_data Terminal_cat Terminal_cat);

// Vertex 1 of Delta[1].
symbol simplex_vertex_one_realization
  : τ (@SelectedFaceRealization zero (succ zero))
≔ @Product_pair_grpd
    (@FaceCode (succ zero) (succ (succ zero)))
    (@StrictFunctorData Terminal_cat WalkingArrow_cat)
    (@face_keep
      zero (succ zero)
      (@face_skip zero zero face_nil))
    (@strict_join_snd_data Terminal_cat Terminal_cat);

// Edge 01 of Delta[2].
symbol simplex_edge_zero_one_realization
  : τ (@SelectedFaceRealization (succ zero) (succ (succ zero)))
≔ @Product_pair_grpd
    (@FaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
    (@StrictFunctorData
      WalkingArrow_cat
      (@Join_cat WalkingArrow_cat Terminal_cat))
    (@face_skip
      (succ (succ zero))
      (succ (succ zero))
      (@face_identity (succ (succ zero))))
    (@strict_join_fst_data WalkingArrow_cat Terminal_cat);

// Edge 02 of Delta[2].
symbol simplex_edge_zero_two_realization
  : τ (@SelectedFaceRealization (succ zero) (succ (succ zero)))
≔ @Product_pair_grpd
    (@FaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
    (@StrictFunctorData
      WalkingArrow_cat
      (@Join_cat WalkingArrow_cat Terminal_cat))
    (@face_keep
      (succ zero)
      (succ (succ zero))
      (@selected_face_code
        zero (succ zero)
        simplex_vertex_zero_realization))
    (@strict_join_map_data
      Terminal_cat Terminal_cat WalkingArrow_cat Terminal_cat
      (@selected_face_data
        zero (succ zero)
        simplex_vertex_zero_realization)
      (@strict_identity_data Terminal_cat));

// Edge 12 of Delta[2].
symbol simplex_edge_one_two_realization
  : τ (@SelectedFaceRealization (succ zero) (succ (succ zero)))
≔ @Product_pair_grpd
    (@FaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
    (@StrictFunctorData
      WalkingArrow_cat
      (@Join_cat WalkingArrow_cat Terminal_cat))
    (@face_keep
      (succ zero)
      (succ (succ zero))
      (@selected_face_code
        zero (succ zero)
        simplex_vertex_one_realization))
    (@strict_join_map_data
      Terminal_cat Terminal_cat WalkingArrow_cat Terminal_cat
      (@selected_face_data
        zero (succ zero)
        simplex_vertex_one_realization)
      (@strict_identity_data Terminal_cat));

// Readable code and whole-functor projections for the five selected faces.
symbol simplex_vertex_zero_code
  : τ (@FaceCode (succ zero) (succ (succ zero)))
≔ @selected_face_code
    zero (succ zero) simplex_vertex_zero_realization;

symbol simplex_vertex_zero_func
  : τ (Functor Terminal_cat WalkingArrow_cat)
≔ @selected_face_func
    zero (succ zero) simplex_vertex_zero_realization;

symbol simplex_vertex_one_code
  : τ (@FaceCode (succ zero) (succ (succ zero)))
≔ @selected_face_code
    zero (succ zero) simplex_vertex_one_realization;

symbol simplex_vertex_one_func
  : τ (Functor Terminal_cat WalkingArrow_cat)
≔ @selected_face_func
    zero (succ zero) simplex_vertex_one_realization;

symbol simplex_edge_zero_one_code
  : τ (@FaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @selected_face_code
    (succ zero) (succ (succ zero))
    simplex_edge_zero_one_realization;

symbol simplex_edge_zero_one_func
  : τ (Functor
      WalkingArrow_cat
      (@Join_cat WalkingArrow_cat Terminal_cat))
≔ @selected_face_func
    (succ zero) (succ (succ zero))
    simplex_edge_zero_one_realization;

symbol simplex_edge_zero_two_code
  : τ (@FaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @selected_face_code
    (succ zero) (succ (succ zero))
    simplex_edge_zero_two_realization;

symbol simplex_edge_zero_two_func
  : τ (Functor
      WalkingArrow_cat
      (@Join_cat WalkingArrow_cat Terminal_cat))
≔ @selected_face_func
    (succ zero) (succ (succ zero))
    simplex_edge_zero_two_realization;

symbol simplex_edge_one_two_code
  : τ (@FaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @selected_face_code
    (succ zero) (succ (succ zero))
    simplex_edge_one_two_realization;

symbol simplex_edge_one_two_func
  : τ (Functor
      WalkingArrow_cat
      (@Join_cat WalkingArrow_cat Terminal_cat))
≔ @selected_face_func
    (succ zero) (succ (succ zero))
    simplex_edge_one_two_realization;
