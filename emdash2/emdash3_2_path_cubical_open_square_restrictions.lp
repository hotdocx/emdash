/*
  Emdash v3.2: restrict native path squares to the four explicit open boxes.

  The constructor-complete native-square eliminator exposes one square's four
  vertices and paths. Each restriction forgets exactly its selected missing
  edge and the filler. Visible restrictions therefore compute to the matching
  three-edge constructor without a face-specific rewrite.
*/

require open emdash.emdash3_2_path_cubical_square_elim;

symbol path_square_restrict_missing_u
  [A : Grpd]
  (S : τ (@PathCube_grpd A (succ (succ zero))))
  : τ (@PathOpenSquareMissingU_grpd A)
≔ @path_cube_square_ind
    A
    (λ _ : τ (@PathCube_grpd A (succ (succ zero))),
      @PathOpenSquareMissingU_grpd A)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ u : τ (@= A x00 x01), λ v : τ (@= A x10 x11),
        λ a : τ (@= A x00 x10), λ b : τ (@= A x01 x11),
          λ _ : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b),
            @path_open_square_missing_u_intro
              A x00 x01 x10 x11 v a b)
    S;

symbol path_square_restrict_missing_v
  [A : Grpd]
  (S : τ (@PathCube_grpd A (succ (succ zero))))
  : τ (@PathOpenSquareMissingV_grpd A)
≔ @path_cube_square_ind
    A
    (λ _ : τ (@PathCube_grpd A (succ (succ zero))),
      @PathOpenSquareMissingV_grpd A)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ u : τ (@= A x00 x01), λ v : τ (@= A x10 x11),
        λ a : τ (@= A x00 x10), λ b : τ (@= A x01 x11),
          λ _ : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b),
            @path_open_square_missing_v_intro
              A x00 x01 x10 x11 u a b)
    S;

symbol path_square_restrict_missing_a
  [A : Grpd]
  (S : τ (@PathCube_grpd A (succ (succ zero))))
  : τ (@PathOpenSquareMissingA_grpd A)
≔ @path_cube_square_ind
    A
    (λ _ : τ (@PathCube_grpd A (succ (succ zero))),
      @PathOpenSquareMissingA_grpd A)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ u : τ (@= A x00 x01), λ v : τ (@= A x10 x11),
        λ a : τ (@= A x00 x10), λ b : τ (@= A x01 x11),
          λ _ : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b),
            @path_open_square_missing_a_intro
              A x00 x01 x10 x11 u v b)
    S;

symbol path_square_restrict_missing_b
  [A : Grpd]
  (S : τ (@PathCube_grpd A (succ (succ zero))))
  : τ (@PathOpenSquareMissingB_grpd A)
≔ @path_cube_square_ind
    A
    (λ _ : τ (@PathCube_grpd A (succ (succ zero))),
      @PathOpenSquareMissingB_grpd A)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ u : τ (@= A x00 x01), λ v : τ (@= A x10 x11),
        λ a : τ (@= A x00 x10), λ b : τ (@= A x01 x11),
          λ _ : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b),
            @path_open_square_missing_b_intro
              A x00 x01 x10 x11 u v a)
    S;

// Raw groupoid functions used by whole Path-map packaging.
symbol path_square_restrict_missing_u_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathCube_grpd A (succ (succ zero)))
      (@PathOpenSquareMissingU_grpd A))
≔ λ S : τ (@PathCube_grpd A (succ (succ zero))),
    @path_square_restrict_missing_u A S;

symbol path_square_restrict_missing_v_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathCube_grpd A (succ (succ zero)))
      (@PathOpenSquareMissingV_grpd A))
≔ λ S : τ (@PathCube_grpd A (succ (succ zero))),
    @path_square_restrict_missing_v A S;

symbol path_square_restrict_missing_a_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathCube_grpd A (succ (succ zero)))
      (@PathOpenSquareMissingA_grpd A))
≔ λ S : τ (@PathCube_grpd A (succ (succ zero))),
    @path_square_restrict_missing_a A S;

symbol path_square_restrict_missing_b_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathCube_grpd A (succ (succ zero)))
      (@PathOpenSquareMissingB_grpd A))
≔ λ S : τ (@PathCube_grpd A (succ (succ zero))),
    @path_square_restrict_missing_b A S;
