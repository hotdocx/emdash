/*
  Emdash v3.2: constructor-complete elimination of native path squares.

  `path_native_square_hom_ind` exposes the existing nested-Sigma sides and
  filler of a square Hom between visible path edges. Combining it with the
  Nat-generic successor eliminator at dimensions one and zero gives
  `path_cube_square_ind`, which exposes every native dimension-two path cube
  as vertices, four paths, and the existing filler `b o u = v o a`.

  Both eliminators operate on derived carriers. They introduce no parallel
  square type or filler. The sole new constructor beta is owned by the stable
  square-Hom eliminator head.
*/

require open emdash.emdash3_2_path_cubical_open_square_fillers;

// Eliminate a native square arrow between visible path edges.
injective symbol path_native_square_hom_ind
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  [u : τ (@= A x00 x01)]
  [v : τ (@= A x10 x11)]
  (Q : τ (Obj (@PathNativeSquareHom_cat A x00 x01 x10 x11 u v)) → Grpd)
  (c : Π a : τ (@= A x00 x10),
       Π b : τ (@= A x01 x11),
       Π alpha : τ (@PathSquareFiller_grpd
         A x00 x01 x10 x11 u v a b),
       τ (Q (@cubical_square
         (Path_cat A) x00 x10 x01 x11 u v a b alpha)))
  (theta : τ (Obj (@PathNativeSquareHom_cat A x00 x01 x10 x11 u v)))
  : τ (Q theta);

rule @path_native_square_hom_ind
      _ _ _ _ _ _ _ _ $c
      (Struct_sigma $a (Struct_sigma $b $alpha))
  ↪ $c $a $b $alpha;

// Eliminate an arbitrary native dimension-two path cube.
symbol path_cube_square_ind
  [A : Grpd]
  (Q : τ (@PathCube_grpd A (succ (succ zero))) → Grpd)
  (c : Π x00 : τ A,
       Π x01 : τ A,
       Π x10 : τ A,
       Π x11 : τ A,
       Π u : τ (@= A x00 x01),
       Π v : τ (@= A x10 x11),
       Π a : τ (@= A x00 x10),
       Π b : τ (@= A x01 x11),
       Π alpha : τ (@PathSquareFiller_grpd
         A x00 x01 x10 x11 u v a b),
       τ (Q (@path_cube_square
         A x00 x01 x10 x11 u v a b alpha)))
  (S : τ (@PathCube_grpd A (succ (succ zero))))
  : τ (Q S)
≔ @path_cube_succ_ind
    A (succ zero)
    Q
    (λ X : τ (@PathCube_grpd A (succ zero)),
      λ Y : τ (@PathCube_grpd A (succ zero)),
        λ theta : τ (Hom (@PathCubicalLevel_cat A (succ zero)) X Y),
          (@path_cube_succ_ind
            A zero
            (λ X0 : τ (@PathCube_grpd A (succ zero)),
              @Pi_grpd
                (@PathCube_grpd A (succ zero))
                (λ Y0 : τ (@PathCube_grpd A (succ zero)),
                  @Pi_grpd
                    (Obj (@Hom_cat
                      (@PathCubicalLevel_cat A (succ zero)) X0 Y0))
                    (λ theta0 : τ (Obj (@Hom_cat
                      (@PathCubicalLevel_cat A (succ zero)) X0 Y0)),
                      Q (@path_cube_succ A (succ zero) X0 Y0 theta0))))
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
                          (λ theta1 : τ (Obj (@Hom_cat
                            (@PathCubicalLevel_cat A (succ zero))
                            (@path_cube_edge A x00 x01 u)
                            Y1)),
                            Q (@path_cube_succ
                              A (succ zero)
                              (@path_cube_edge A x00 x01 u)
                              Y1 theta1)))
                      (λ x10 : τ A,
                        λ x11 : τ A,
                          λ v : τ (@= A x10 x11),
                            λ theta1 : τ (Obj (@PathNativeSquareHom_cat
                              A x00 x01 x10 x11 u v)),
                              @path_native_square_hom_ind
                                A x00 x01 x10 x11 u v
                                (λ theta2 : τ (Obj (@PathNativeSquareHom_cat
                                  A x00 x01 x10 x11 u v)),
                                  Q (@path_cube_succ
                                    A (succ zero)
                                    (@path_cube_edge A x00 x01 u)
                                    (@path_cube_edge A x10 x11 v)
                                    theta2))
                                (λ a : τ (@= A x00 x10),
                                  λ b : τ (@= A x01 x11),
                                    λ alpha : τ (@PathSquareFiller_grpd
                                      A x00 x01 x10 x11 u v a b),
                                      c x00 x01 x10 x11 u v a b alpha)
                                theta1)
                      Y0)
            X)
          Y theta)
    S;
