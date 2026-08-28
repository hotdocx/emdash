/*
  Emdash v3.2: variable-dimensional object decoder for right-Gray cubes.

  The recursion is uniform in the target category:

    decode_n : Pi C,
      StrictFunctor(GrayCubePos_R(n),C)
        -> Obj(CubicalLevel_cat(C,succ n)).

  Dimension one evaluates a strict walking map at the two endpoints and the
  generator. At a successor, right curry turns H into a strict walking map
  whose generator is a transformation between strict lower-dimensional
  diagrams. The selected strict transformation-graph code gives a map into
  LaxArrow(C), the induction hypothesis decodes it there, and the canonical
  cubical-level shift returns the desired level over C.

  This is internal Nat recursion over categories, strict codes, transformations
  and whole graph action. It adds no dimension-specific filler, source-text
  generator, tensor parameter action, inverse decoder, or mapping-category
  equivalence.
*/

require open emdash.emdash3_2_gray_transformation_graph_profile;
require open emdash.emdash3_2_cubical_levels;
require open emdash.emdash3_2_semicubical_frames;

// Iterating cubical levels after one LaxArrow step agrees with adding one
// more successor to the original ambient category.
symbol cubical_level_shift_path
  (C : Cat)
  (n : τ Nat_grpd)
  : τ (@=
      (Obj Cat_cat)
      (@CubicalLevel_cat (@LaxArrow_cat C) (succ n))
      (@CubicalLevel_cat C (succ (succ n))))
≔ @nat_elim
    (λ k : τ Nat_grpd,
      @=
        (Obj Cat_cat)
        (@CubicalLevel_cat (@LaxArrow_cat C) (succ k))
        (@CubicalLevel_cat C (succ (succ k))))
    (@eq_refl
      (Obj Cat_cat)
      (@CubicalLevel_cat (@LaxArrow_cat C) (succ zero)))
    (λ k : τ Nat_grpd,
      λ p : τ (@=
        (Obj Cat_cat)
        (@CubicalLevel_cat (@LaxArrow_cat C) (succ k))
        (@CubicalLevel_cat C (succ (succ k)))),
        @eq_ap
          (Obj Cat_cat)
          (Obj Cat_cat)
          (λ D : Cat, @LaxArrow_cat D)
          (@CubicalLevel_cat (@LaxArrow_cat C) (succ k))
          (@CubicalLevel_cat C (succ (succ k)))
          p)
    n;

symbol cubical_level_shift_func
  (C : Cat)
  (n : τ Nat_grpd)
  : τ (Functor
      (@CubicalLevel_cat (@LaxArrow_cat C) (succ n))
      (@CubicalLevel_cat C (succ (succ n))))
≔ @path_to_hom
    Cat_cat
    (@CubicalLevel_cat (@LaxArrow_cat C) (succ n))
    (@CubicalLevel_cat C (succ (succ n)))
    (@cubical_level_shift_path C n);

// Uniform family of object-level decoders at predecessor index n.
symbol GrayCubeObservationFamily
  (n : τ Nat_grpd)
  : Grpd
≔ @Pi_grpd
    (Obj Cat_cat)
    (λ C : Cat,
      @Function_grpd
        (@StrictFunctor (@GrayCubePos_R n) C)
        (Obj (@CubicalLevel_cat C (succ n))));

// Dimension-one observation of a strict walking-arrow realization.
symbol gray_cube_decode_one
  [C : Cat]
  (H : τ (@StrictFunctor WalkingArrow_cat C))
  : τ (Obj (@CubicalLevel_cat C (succ zero)))
≔ @lax_edge
    C
    (@fapp0
      WalkingArrow_cat C
      (@strict_functor WalkingArrow_cat C H)
      walking_arrow_src)
    (@fapp0
      WalkingArrow_cat C
      (@strict_functor WalkingArrow_cat C H)
      walking_arrow_tgt)
    (@fapp1_fapp0
      WalkingArrow_cat C
      (@strict_functor WalkingArrow_cat C H)
      walking_arrow_src walking_arrow_tgt
      walking_arrow_generator);

// Curry a successor cube into a strict walking map of lower strict diagrams.
symbol gray_cube_step_curry_data
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R (succ n)) C))
  : τ (@StrictFunctor
      WalkingArrow_cat
      (@GrayHom_lax (@GrayCubePos_R n) C))
≔ @gray_curry_R
    WalkingArrow_cat
    (@GrayCubePos_R n)
    C
    H;

symbol gray_cube_step_curry_func
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R (succ n)) C))
  : τ (Functor
      WalkingArrow_cat
      (@GrayHom_lax (@GrayCubePos_R n) C))
≔ @strict_functor
    WalkingArrow_cat
    (@GrayHom_lax (@GrayCubePos_R n) C)
    (@gray_cube_step_curry_data C n H);

symbol gray_cube_step_source_data
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R (succ n)) C))
  : τ (@StrictFunctor (@GrayCubePos_R n) C)
≔ @fapp0
    WalkingArrow_cat
    (@GrayHom_lax (@GrayCubePos_R n) C)
    (@gray_cube_step_curry_func C n H)
    walking_arrow_src;

symbol gray_cube_step_target_data
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R (succ n)) C))
  : τ (@StrictFunctor (@GrayCubePos_R n) C)
≔ @fapp0
    WalkingArrow_cat
    (@GrayHom_lax (@GrayCubePos_R n) C)
    (@gray_cube_step_curry_func C n H)
    walking_arrow_tgt;

symbol gray_cube_step_transf
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R (succ n)) C))
  : τ (Transf
      (@strict_functor
        (@GrayCubePos_R n) C
        (@gray_cube_step_source_data C n H))
      (@strict_functor
        (@GrayCubePos_R n) C
        (@gray_cube_step_target_data C n H)))
≔ @fapp1_fapp0
    WalkingArrow_cat
    (@GrayHom_lax (@GrayCubePos_R n) C)
    (@gray_cube_step_curry_func C n H)
    walking_arrow_src walking_arrow_tgt
    walking_arrow_generator;

// Strict code for the lower-dimensional transformation graph in LaxArrow(C).
symbol gray_cube_step_graph_data
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R (succ n)) C))
  : τ (@StrictFunctor
      (@GrayCubePos_R n)
      (@LaxArrow_cat C))
≔ @strict_gray_transf_graph
    (@GrayCubePos_R n)
    C
    (@gray_cube_step_source_data C n H)
    (@gray_cube_step_target_data C n H)
    (@gray_cube_step_transf C n H);

// Successor of the uniform decoder family.
symbol gray_cube_decode_step
  (n : τ Nat_grpd)
  (rec : τ (@GrayCubeObservationFamily n))
  (C : Cat)
  (H : τ (@StrictFunctor (@GrayCubePos_R (succ n)) C))
  : τ (Obj (@CubicalLevel_cat C (succ (succ n))))
≔ @fapp0
    (@CubicalLevel_cat (@LaxArrow_cat C) (succ n))
    (@CubicalLevel_cat C (succ (succ n)))
    (@cubical_level_shift_func C n)
    (rec
      (@LaxArrow_cat C)
      (@gray_cube_step_graph_data C n H));

// Internal Nat recursion, uniform in the target category.
symbol gray_cube_observation_all
  (n : τ Nat_grpd)
  : τ (@GrayCubeObservationFamily n)
≔ @nat_elim
    (λ k : τ Nat_grpd, @GrayCubeObservationFamily k)
    (λ C : Cat,
      λ H : τ (@StrictFunctor (@GrayCubePos_R zero) C),
        @gray_cube_decode_one C H)
    (λ k : τ Nat_grpd,
      λ rec : τ (@GrayCubeObservationFamily k),
      λ C : Cat,
      λ H : τ (@StrictFunctor (@GrayCubePos_R (succ k)) C),
        @gray_cube_decode_step k rec C H)
    n;

// Public object observation for a strict realization of the (n+1)-cube.
symbol gray_cube_observation
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R n) C))
  : τ (Obj (@CubicalLevel_cat C (succ n)))
≔ @gray_cube_observation_all n C H;

// Apply the already-internal immediate coface family to a decoded cube.  At
// dimension n+1 this returns 2(n+1) native n-faces, so squares have four edges
// and cubes have six square faces without a dimension-specific boundary
// record.
symbol gray_cube_immediate_faces
  [C : Cat]
  (n : τ Nat_grpd)
  (H : τ (@StrictFunctor (@GrayCubePos_R n) C))
  : τ (@FiniteFamily
      (Obj (@CubicalLevel_cat C n))
      (@CubeImmediateFaceCount (succ n)))
≔ @finite_family_map
    (Functor
      (@CubicalLevel_cat C (succ n))
      (@CubicalLevel_cat C n))
    (Obj (@CubicalLevel_cat C n))
    (λ face : τ (Functor
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)),
      @fapp0
        (@CubicalLevel_cat C (succ n))
        (@CubicalLevel_cat C n)
        face
        (@gray_cube_observation C n H))
    (@CubeImmediateFaceCount (succ n))
    (@cube_immediate_face_actions C n);
