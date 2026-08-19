/*
  Four strict triangle cofaces of the ordinal tetrahedron.

  Face 012 is the old-triangle join inclusion.  Faces 013, 023, and 123
  retain one of the three old edges and the newly joined final vertex.  Each
  realization pairs its computing FaceCode with an existing strict-profile
  join functor; no generic face decoder or new action rule is introduced.

  All six shared edges compute at the face-code level.  The three old-base
  edges also agree as composite whole functors.  The three edges involving the
  new vertex expose a later join-map-composition comparison and are not folded
  here by a local rewrite.
*/

require open emdash.emdash3_2_coherent_nerve_levels;

// Triangle 012: omit the newly joined vertex 3.
symbol simplex_triangle_zero_one_two_realization
  : τ (@SelectedFaceRealization
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @Product_pair_grpd
    (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
    (@StrictFunctorData
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
    (@face_skip
      (succ (succ (succ zero)))
      (succ (succ (succ zero)))
      (@face_identity (succ (succ (succ zero)))))
    (@strict_join_fst_data
      (@DirectedSimplex_cat (succ (succ zero)))
      Terminal_cat);

// Triangle 013: retain old edge 01 and the new final vertex.
symbol simplex_triangle_zero_one_three_realization
  : τ (@SelectedFaceRealization
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @Product_pair_grpd
    (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
    (@StrictFunctorData
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
    (@face_keep
      (succ (succ zero))
      (succ (succ (succ zero)))
      simplex_edge_zero_one_code)
    (@strict_join_map_data
      WalkingArrow_cat Terminal_cat
      (@DirectedSimplex_cat (succ (succ zero))) Terminal_cat
      (@selected_face_data
        (succ zero) (succ (succ zero))
        simplex_edge_zero_one_realization)
      (@strict_identity_data Terminal_cat));

// Triangle 023: retain old edge 02 and the new final vertex.
symbol simplex_triangle_zero_two_three_realization
  : τ (@SelectedFaceRealization
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @Product_pair_grpd
    (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
    (@StrictFunctorData
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
    (@face_keep
      (succ (succ zero))
      (succ (succ (succ zero)))
      simplex_edge_zero_two_code)
    (@strict_join_map_data
      WalkingArrow_cat Terminal_cat
      (@DirectedSimplex_cat (succ (succ zero))) Terminal_cat
      (@selected_face_data
        (succ zero) (succ (succ zero))
        simplex_edge_zero_two_realization)
      (@strict_identity_data Terminal_cat));

// Triangle 123: retain old edge 12 and the new final vertex.
symbol simplex_triangle_one_two_three_realization
  : τ (@SelectedFaceRealization
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @Product_pair_grpd
    (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
    (@StrictFunctorData
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
    (@face_keep
      (succ (succ zero))
      (succ (succ (succ zero)))
      simplex_edge_one_two_code)
    (@strict_join_map_data
      WalkingArrow_cat Terminal_cat
      (@DirectedSimplex_cat (succ (succ zero))) Terminal_cat
      (@selected_face_data
        (succ zero) (succ (succ zero))
        simplex_edge_one_two_realization)
      (@strict_identity_data Terminal_cat));

// Readable code projections.
symbol simplex_triangle_zero_one_two_code
  : τ (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @selected_face_code
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_zero_one_two_realization;

symbol simplex_triangle_zero_one_three_code
  : τ (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @selected_face_code
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_zero_one_three_realization;

symbol simplex_triangle_zero_two_three_code
  : τ (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @selected_face_code
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_zero_two_three_realization;

symbol simplex_triangle_one_two_three_code
  : τ (@FaceCode
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero)))))
≔ @selected_face_code
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_one_two_three_realization;

// Readable whole-functor projections.
symbol simplex_triangle_zero_one_two_func
  : τ (Functor
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
≔ @selected_face_func
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_zero_one_two_realization;

symbol simplex_triangle_zero_one_three_func
  : τ (Functor
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
≔ @selected_face_func
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_zero_one_three_realization;

symbol simplex_triangle_zero_two_three_func
  : τ (Functor
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
≔ @selected_face_func
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_zero_two_three_realization;

symbol simplex_triangle_one_two_three_func
  : τ (Functor
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero)))))
≔ @selected_face_func
    (succ (succ zero)) (succ (succ (succ zero)))
    simplex_triangle_one_two_three_realization;
