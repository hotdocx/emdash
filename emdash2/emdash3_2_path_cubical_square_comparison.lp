/*
  Emdash v3.2: the dimension-one path-edge/square comparison.

  A native square between visible path edges has sides a,b and filler

    alpha : b o u = v o a.

  Two right-J eliminations turn that square into equality of the nested-Sigma
  edge objects. Conversely, the existing core-inclusion hom action turns an
  equality of edge objects into a native square. The readback lifts wholely on
  the path core of the native square Hom, so every higher equality action is
  retained through Path_map.

  Extending the readback source from Core(Hom) to the native Hom itself is
  deliberately not assumed here: that is exactly the subsequent
  groupoidality-closure theorem. This module is transparent and rule-free. It
  adds no square, path, inverse, rewrite, unifier, or endpoint collapse.
*/

require open emdash.emdash3_2_path_cubical_levels;

// Native category of squares between two visible path edges.
symbol PathNativeSquareHom_cat
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  : Cat
≔ @Hom_cat
    (@PathCubicalLevel_cat A (succ zero))
    (@path_cube_edge A x00 x01 u)
    (@path_cube_edge A x10 x11 v);

// Equality groupoid between those two edge objects.
symbol PathEdgeEquality_grpd
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  : Grpd
≔ @=
    (@PathCube_grpd A (succ zero))
    (@path_cube_edge A x00 x01 u)
    (@path_cube_edge A x10 x11 v);

// Fixed-source square readback, reduced by right-J on b.
symbol path_square_edge_path_same_source
  [A : Grpd]
  [x x01 x11 : τ A]
  (u : τ (@= A x x01))
  (v : τ (@= A x x11))
  (b : τ (@= A x01 x11))
  (alpha : τ (@=
    (@= A x x11)
    (@comp_fapp0 (Path_cat A) x x01 x11 b u)
    (@comp_fapp0
      (Path_cat A) x x x11 v (@eq_refl A x))))
  : τ (@=
      (@PathCube_grpd A (succ zero))
      (@path_cube_edge A x x01 u)
      (@path_cube_edge A x x11 v))
≔ (@ind_eqr
      A x11
      (λ z : τ A, λ b0 : τ (@= A z x11),
        @Pi_grpd
          (@= A x z)
          (λ u0 : τ (@= A x z),
            @Pi_grpd
              (@= A x x11)
              (λ v0 : τ (@= A x x11),
                @Pi_grpd
                  (@=
                    (@= A x x11)
                    (@comp_fapp0 (Path_cat A) x z x11 b0 u0)
                    (@comp_fapp0
                      (Path_cat A) x x x11 v0 (@eq_refl A x)))
                  (λ _ : τ (@=
                    (@= A x x11)
                    (@comp_fapp0 (Path_cat A) x z x11 b0 u0)
                    (@comp_fapp0
                      (Path_cat A) x x x11 v0 (@eq_refl A x))),
                    @=
                      (@PathCube_grpd A (succ zero))
                      (@path_cube_edge A x z u0)
                      (@path_cube_edge A x x11 v0)))))
      (λ u0 : τ (@= A x x11),
        λ v0 : τ (@= A x x11),
          λ alpha0 : τ (@= (@= A x x11) u0 v0),
            @eq_ap
              (@= A x x11)
              (@PathCube_grpd A (succ zero))
              (λ w : τ (@= A x x11),
                @path_cube_edge A x x11 w)
              u0 v0 alpha0)
      x01 b)
    u v alpha;

// General visible square readback, reduced by right-J on a and then b.
symbol path_square_edge_path
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b))
  : τ (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v)
≔ (@ind_eqr
      A x10
      (λ z : τ A, λ a0 : τ (@= A z x10),
        @Pi_grpd A
          (λ z01 : τ A,
            @Pi_grpd
              (@= A z z01)
              (λ u0 : τ (@= A z z01),
                @Pi_grpd A
                  (λ z11 : τ A,
                    @Pi_grpd
                      (@= A x10 z11)
                      (λ v0 : τ (@= A x10 z11),
                        @Pi_grpd
                          (@= A z01 z11)
                          (λ b0 : τ (@= A z01 z11),
                            @Pi_grpd
                              (@=
                                (@= A z z11)
                                (@comp_fapp0
                                  (Path_cat A) z z01 z11 b0 u0)
                                (@comp_fapp0
                                  (Path_cat A) z x10 z11 v0 a0))
                              (λ _ : τ (@=
                                (@= A z z11)
                                (@comp_fapp0
                                  (Path_cat A) z z01 z11 b0 u0)
                                (@comp_fapp0
                                  (Path_cat A) z x10 z11 v0 a0)),
                                @=
                                  (@PathCube_grpd A (succ zero))
                                  (@path_cube_edge A z z01 u0)
                                  (@path_cube_edge A x10 z11 v0))))))))
      (λ z01 : τ A,
        λ u0 : τ (@= A x10 z01),
          λ z11 : τ A,
            λ v0 : τ (@= A x10 z11),
              λ b0 : τ (@= A z01 z11),
                λ alpha0 : τ (@=
                  (@= A x10 z11)
                  (@comp_fapp0 (Path_cat A) x10 z01 z11 b0 u0)
                  (@comp_fapp0
                    (Path_cat A) x10 x10 z11 v0 (@eq_refl A x10))),
                  @path_square_edge_path_same_source
                    A x10 z01 z11 u0 v0 b0 alpha0)
      x00 a)
    x01 u x11 v b alpha;

// Read an arbitrary native square object through its nested Sigma fields.
symbol path_native_square_edge_path
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (theta : τ (Obj (@PathNativeSquareHom_cat
    A x00 x01 x10 x11 u v)))
  : τ (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v)
≔ @path_square_edge_path
    A x00 x01 x10 x11
    u v
    (sigma_Fst theta)
    (sigma_Fst (sigma_Snd theta))
    (sigma_Snd (sigma_Snd theta));

// Whole equality action of square readback on the native Hom's path core.
symbol path_native_square_core_readback_func
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  : τ (Functor
      (Path_cat (Obj (@PathNativeSquareHom_cat
        A x00 x01 x10 x11 u v)))
      (Path_cat (@PathEdgeEquality_grpd
        A x00 x01 x10 x11 u v)))
≔ @path_map_func
    (Obj (@PathNativeSquareHom_cat A x00 x01 x10 x11 u v))
    (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v)
    (λ theta : τ (Obj (@PathNativeSquareHom_cat
      A x00 x01 x10 x11 u v)),
      @path_native_square_edge_path
        A x00 x01 x10 x11 u v theta);

// Reverse whole comparison: the existing core-inclusion hom action.
symbol path_edge_path_to_native_square_func
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  : τ (Functor
      (Path_cat (@PathEdgeEquality_grpd
        A x00 x01 x10 x11 u v))
      (@PathNativeSquareHom_cat A x00 x01 x10 x11 u v))
≔ @core_incl_hom_func
    (@PathCubicalLevel_cat A (succ zero))
    (@path_cube_edge A x00 x01 u)
    (@path_cube_edge A x10 x11 v);

// First retained equality action of the readback function.
symbol path_native_square_core_readback_hom_func
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (S T : τ (Obj (@PathNativeSquareHom_cat
    A x00 x01 x10 x11 u v)))
  : τ (Functor
      (Path_cat (@=
        (Obj (@PathNativeSquareHom_cat A x00 x01 x10 x11 u v))
        S T))
      (Path_cat (@=
        (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v)
        (@path_native_square_edge_path
          A x00 x01 x10 x11 u v S)
        (@path_native_square_edge_path
          A x00 x01 x10 x11 u v T))))
≔ @fapp1_func
    (Path_cat (Obj (@PathNativeSquareHom_cat
      A x00 x01 x10 x11 u v)))
    (Path_cat (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v))
    (@path_native_square_core_readback_func
      A x00 x01 x10 x11 u v)
    S T;
