/*
  Emdash v3.2: low-dimensional structured/native path-cube comparison.

  One generic successor decoder turns a native cubical arrow into the
  structured Sigma/PathOver successor whenever the preceding level supplies
  an object decoder and an arrow-to-path readback.  It yields native-to-
  structured decoders in dimensions zero, one, and two.

  Dimension zero has both selected round trips, and every native dimension-one
  edge is recovered propositionally.  Dimension two decodes using the active
  pointwise square readback.  Advancing to dimension three requires a
  cube-to-square equality readback.  A typed attempted derivation reaches the
  exact missing constructor-visible cubical identity comparison before any
  whole arrow/pasting action can be assembled.
*/

require open emdash.emdash3_2_path_cubical_structured_recursion;
require open emdash.emdash3_2_path_cubical_face_naturality;
require open emdash.emdash3_2_path_cubical_square_elim;

symbol structured_step_decode_path
  [S : τ PathCubeSpecU]
  [C : Cat]
  (decode : τ (Obj C) → τ (@path_cube_spec_cube S))
  (read : Π X : τ (Obj C), Π Y : τ (Obj C),
    τ (Obj (@Hom_cat C X Y)) → τ (@= (Obj C) X Y))
  (Z : τ (Obj (@CubicalArrow_cat C)))
  : τ (@=
      (@path_cube_spec_cube S)
      (decode (sigma_Fst Z))
      (decode (sigma_Fst (sigma_Snd Z))))
≔ @eq_ap
    (Obj C)
    (@path_cube_spec_cube S)
    decode
    (sigma_Fst Z)
    (sigma_Fst (sigma_Snd Z))
    (read
      (sigma_Fst Z)
      (sigma_Fst (sigma_Snd Z))
      (sigma_Snd (sigma_Snd Z)));

symbol structured_step_decode_view
  [S : τ PathCubeSpecU]
  [C : Cat]
  (decode : τ (Obj C) → τ (@path_cube_spec_cube S))
  (read : Π X : τ (Obj C), Π Y : τ (Obj C),
    τ (Obj (@Hom_cat C X Y)) → τ (@= (Obj C) X Y))
  (Z : τ (Obj (@CubicalArrow_cat C)))
  : τ (@SigmaPathView
      (@path_cube_spec_boundary S)
      (λ b : τ (@path_cube_spec_boundary S), @path_cube_spec_rel S b)
      (decode (sigma_Fst Z))
      (decode (sigma_Fst (sigma_Snd Z))))
≔ @sigma_path_encode
    (@path_cube_spec_boundary S)
    (λ b : τ (@path_cube_spec_boundary S), @path_cube_spec_rel S b)
    (decode (sigma_Fst Z))
    (decode (sigma_Fst (sigma_Snd Z)))
    (@structured_step_decode_path S C decode read Z);

symbol structured_step_decode
  [S : τ PathCubeSpecU]
  [C : Cat]
  (decode : τ (Obj C) → τ (@path_cube_spec_cube S))
  (read : Π X : τ (Obj C), Π Y : τ (Obj C),
    τ (Obj (@Hom_cat C X Y)) → τ (@= (Obj C) X Y))
  (Z : τ (Obj (@CubicalArrow_cat C)))
  : τ (@path_cube_spec_cube (@path_cube_spec_step S))
≔ @path_cube_spec_step_cube_intro
    S
    (decode (sigma_Fst Z))
    (decode (sigma_Fst (sigma_Snd Z)))
    (sigma_path_base
      (@structured_step_decode_view S C decode read Z))
    (sigma_path_fibre
      (@structured_step_decode_view S C decode read Z));

symbol path_structured_native_decode0
  [A : Grpd]
  (x : τ (@PathCube_grpd A zero))
  : τ (@StructuredPathCubeRec_grpd A zero)
≔ @path_cube_spec_cube_intro (@path_cube_spec_base A) tt x;

symbol path_cube0_arrow_path
  [A : Grpd]
  [x y : τ (@PathCube_grpd A zero)]
  (theta : τ (Obj (@Hom_cat (@PathCubicalLevel_cat A zero) x y)))
  : τ (@= (@PathCube_grpd A zero) x y)
≔ theta;

// Pointwise arrow-to-equality capability needed by one successor decode.
// This is deliberately weaker than a whole native-Hom readback functor.
symbol PathCubeReadback_grpd
  (A : Grpd)
  (n : τ Nat_grpd)
  : Grpd
≔ @Pi_grpd
    (@PathCube_grpd A n)
    (λ X : τ (@PathCube_grpd A n),
      @Pi_grpd
        (@PathCube_grpd A n)
        (λ Y : τ (@PathCube_grpd A n),
          @Function_grpd
            (Obj (@Hom_cat (@PathCubicalLevel_cat A n) X Y))
            (@= (@PathCube_grpd A n) X Y)));

symbol path_cube_readback0
  (A : Grpd)
  : τ (@PathCubeReadback_grpd A zero)
≔ λ x : τ A, λ y : τ A,
    λ theta : τ (Obj (@Hom_cat (Path_cat A) x y)), theta;

symbol path_cube_readback1
  (A : Grpd)
  : τ (@PathCubeReadback_grpd A (succ zero))
≔ λ X : τ (@PathCube_grpd A (succ zero)),
    λ Y : τ (@PathCube_grpd A (succ zero)),
      λ theta : τ (Obj (@Hom_cat
        (@PathCubicalLevel_cat A (succ zero)) X Y)),
        @path_native_square_path A X Y theta;

symbol path_structured_native_decode1
  [A : Grpd]
  (Z : τ (@PathCube_grpd A (succ zero)))
  : τ (@StructuredPathCubeRec_grpd A (succ zero))
≔ @structured_step_decode
    (@path_cube_spec_base A)
    (Path_cat A)
    (λ x : τ A, @path_structured_native_decode0 A x)
    (@path_cube_readback0 A)
    Z;
symbol path_structured_native_decode2
  [A : Grpd]
  (Z : τ (@PathCube_grpd A (succ (succ zero))))
  : τ (@StructuredPathCubeRec_grpd A (succ (succ zero)))
≔ @structured_step_decode
    (@path_cube_spec A (succ zero))
    (@PathCubicalLevel_cat A (succ zero))
    (λ X : τ (@PathCube_grpd A (succ zero)),
      @path_structured_native_decode1 A X)
    (@path_cube_readback1 A)
    Z;

// The dimension-three decoder is completely determined once the next
// pointwise cube-to-square-equality readback is supplied.  No such readback
// is asserted here; constructing it requires the missing whole recursive
// action through the preceding TypeEquiv family.
symbol path_structured_native_decode3_with_readback
  [A : Grpd]
  (read2 : τ (@PathCubeReadback_grpd A (succ (succ zero))))
  (Z : τ (@PathCube_grpd A (succ (succ (succ zero)))))
  : τ (@StructuredPathCubeRec_grpd A (succ (succ (succ zero))))
≔ @structured_step_decode
    (@path_cube_spec A (succ (succ zero)))
    (@PathCubicalLevel_cat A (succ (succ zero)))
    (λ S : τ (@PathCube_grpd A (succ (succ zero))),
      @path_structured_native_decode2 A S)
    read2
    Z;

symbol path_structured_native_decode1_realize_path
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@=
      (@PathCube_grpd A (succ zero))
      ((@path_structured_path_cube_realize_function A (succ zero))
        (@path_structured_native_decode1
          A (@path_cube_edge A x y p)))
      (@path_cube_edge A x y p))
≔ @ind_eqr
    A y
    (λ x0 : τ A, λ p0 : τ (@= A x0 y),
      @=
        (@PathCube_grpd A (succ zero))
        ((@path_structured_path_cube_realize_function A (succ zero))
          (@path_structured_native_decode1
            A (@path_cube_edge A x0 y p0)))
        (@path_cube_edge A x0 y p0))
    (@eq_refl
      (@PathCube_grpd A (succ zero))
      (@path_cube_edge A y y (@eq_refl A y)))
    x p;

symbol path_structured_native_decode0_realize_path
  [A : Grpd]
  (z : τ (@StructuredPathCubeRec_grpd A zero))
  : τ (@=
      (@StructuredPathCubeRec_grpd A zero)
      (@path_structured_native_decode0
        A ((@path_structured_path_cube_realize_function A zero) z))
      z)
≔ @sigma_ind
    Unit_grpd
    (λ _ : τ Unit_grpd, A)
    (λ z0 : τ (@StructuredPathCubeRec_grpd A zero),
      @=
        (@StructuredPathCubeRec_grpd A zero)
        (@path_structured_native_decode0
          A ((@path_structured_path_cube_realize_function A zero) z0))
        z0)
    (λ u : τ Unit_grpd,
      λ x : τ A,
        @ind_unit
          (λ u0 : τ Unit_grpd,
            @=
              (@StructuredPathCubeRec_grpd A zero)
              (@path_structured_native_decode0 A x)
              (@path_cube_spec_cube_intro
                (@path_cube_spec_base A) u0 x))
          (@eq_refl
            (@StructuredPathCubeRec_grpd A zero)
            (@path_cube_spec_cube_intro (@path_cube_spec_base A) tt x))
          u)
    z;

symbol path_structured_native_decode1_realize_all_path
  [A : Grpd]
  (Z : τ (@PathCube_grpd A (succ zero)))
  : τ (@=
      (@PathCube_grpd A (succ zero))
      ((@path_structured_path_cube_realize_function A (succ zero))
        (@path_structured_native_decode1 A Z))
      Z)
≔ @path_cube_succ_ind
    A zero
    (λ Z0 : τ (@PathCube_grpd A (succ zero)),
      @=
        (@PathCube_grpd A (succ zero))
        ((@path_structured_path_cube_realize_function A (succ zero))
          (@path_structured_native_decode1 A Z0))
        Z0)
    (λ x : τ A,
      λ y : τ A,
        λ p : τ (@= A x y),
          @path_structured_native_decode1_realize_path A x y p)
    Z;
