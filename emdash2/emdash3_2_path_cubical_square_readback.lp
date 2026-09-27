/*
  Emdash v3.2: generic pointwise readback of native path squares.

  The Nat-generic successor eliminator exposes arbitrary dimension-one cube
  objects as visible path edges. Applying it to both endpoints lets the
  dimension-one J comparison read every native square

    theta : Hom_{PathCubicalLevel(A,1)}(X,Y)

  as equality X = Y. On visible edges and a visible square, this computes to
  the existing `path_square_edge_path` term.

  The raw readback has a whole equality action on Core(Hom) through Path_map;
  the reverse whole map is the existing core-inclusion hom action. A functor
  from the native Hom itself to the Path category is deliberately absent: its
  higher action on cubes and identity/pasting coherence are exactly the
  groupoidality-closure prerequisite. This module is transparent and
  rule-free.
*/

require open emdash.emdash3_2_path_cubical_square_comparison;
require open emdash.emdash3_2_path_cubical_successor_elim;

// Every native square determines equality of its arbitrary path-edge objects.
symbol path_native_square_path
  [A : Grpd]
  (X Y : τ (@PathCube_grpd A (succ zero)))
  (theta : τ (Obj (@Hom_cat
    (@PathCubicalLevel_cat A (succ zero)) X Y)))
  : τ (@= (@PathCube_grpd A (succ zero)) X Y)
≔ (@path_cube_succ_ind
      A zero
      (λ X0 : τ (@PathCube_grpd A (succ zero)),
        @Pi_grpd
          (@PathCube_grpd A (succ zero))
          (λ Y0 : τ (@PathCube_grpd A (succ zero)),
            @Pi_grpd
              (Obj (@Hom_cat
                (@PathCubicalLevel_cat A (succ zero)) X0 Y0))
              (λ _ : τ (Obj (@Hom_cat
                (@PathCubicalLevel_cat A (succ zero)) X0 Y0)),
                @= (@PathCube_grpd A (succ zero)) X0 Y0)))
      (λ x00 : τ A,
        λ x01 : τ A,
          λ u : τ (@= A x00 x01),
            λ Y0 : τ (@PathCube_grpd A (succ zero)),
              @path_cube_succ_ind
                A zero
                (λ Y1 : τ (@PathCube_grpd A (succ zero)),
                  @Pi_grpd
                    (Obj (@Hom_cat
                      (@PathCubicalLevel_cat A (succ zero))
                      (@path_cube_edge A x00 x01 u)
                      Y1))
                    (λ _ : τ (Obj (@Hom_cat
                      (@PathCubicalLevel_cat A (succ zero))
                      (@path_cube_edge A x00 x01 u)
                      Y1)),
                      @=
                        (@PathCube_grpd A (succ zero))
                        (@path_cube_edge A x00 x01 u)
                        Y1))
                (λ x10 : τ A,
                  λ x11 : τ A,
                    λ v : τ (@= A x10 x11),
                      λ theta0 : τ (Obj (@PathNativeSquareHom_cat
                        A x00 x01 x10 x11 u v)),
                        @path_square_edge_path
                          A x00 x01 x10 x11
                          u v
                          (sigma_Fst theta0)
                          (sigma_Fst (sigma_Snd theta0))
                          (sigma_Snd (sigma_Snd theta0)))
                Y0)
      X)
    Y theta;

// Equality action of the generic readback on the path core of one native Hom.
symbol path_native_square_readback_core_func
  [A : Grpd]
  (X Y : τ (@PathCube_grpd A (succ zero)))
  : τ (Functor
      (Path_cat (Obj (@Hom_cat
        (@PathCubicalLevel_cat A (succ zero)) X Y)))
      (Path_cat (@= (@PathCube_grpd A (succ zero)) X Y)))
≔ @path_map_func
    (Obj (@Hom_cat (@PathCubicalLevel_cat A (succ zero)) X Y))
    (@= (@PathCube_grpd A (succ zero)) X Y)
    (λ theta : τ (Obj (@Hom_cat
      (@PathCubicalLevel_cat A (succ zero)) X Y)),
      @path_native_square_path A X Y theta);

// Existing reverse whole map from equality of edges to native squares.
symbol path_edge_equality_to_native_square_func
  [A : Grpd]
  (X Y : τ (@PathCube_grpd A (succ zero)))
  : τ (Functor
      (Path_cat (@= (@PathCube_grpd A (succ zero)) X Y))
      (@Hom_cat (@PathCubicalLevel_cat A (succ zero)) X Y))
≔ @core_incl_hom_func
    (@PathCubicalLevel_cat A (succ zero)) X Y;

// First retained equality action of the generic readback.
symbol path_native_square_readback_core_hom_func
  [A : Grpd]
  [X Y : τ (@PathCube_grpd A (succ zero))]
  (S T : τ (Obj (@Hom_cat
    (@PathCubicalLevel_cat A (succ zero)) X Y)))
  : τ (Functor
      (Path_cat (@=
        (Obj (@Hom_cat (@PathCubicalLevel_cat A (succ zero)) X Y))
        S T))
      (Path_cat (@=
        (@= (@PathCube_grpd A (succ zero)) X Y)
        (@path_native_square_path A X Y S)
        (@path_native_square_path A X Y T))))
≔ @fapp1_func
    (Path_cat (Obj (@Hom_cat
      (@PathCubicalLevel_cat A (succ zero)) X Y)))
    (Path_cat (@= (@PathCube_grpd A (succ zero)) X Y))
    (@path_native_square_readback_core_func A X Y)
    S T;
