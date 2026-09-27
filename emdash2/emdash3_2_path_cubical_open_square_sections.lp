/*
  Emdash v3.2: restriction-section laws for all four open-square fillers.

  The shared three-edge-frame eliminator reduces each arbitrary box to its
  visible constructor. Filling and then restricting forgets the newly chosen
  edge and filler, so every branch is reflexivity. These are groupoid equality
  proofs, not category-level inverse functors or filler uniqueness.
*/

require open emdash.emdash3_2_path_cubical_open_square_restrictions;

symbol path_open_square_missing_u_section
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (@=
      (@PathOpenSquareMissingU_grpd A)
      (@path_square_restrict_missing_u
        A (@path_open_square_fill_missing_u A box))
      box)
≔ @path_open_square_frame_ind
    A (@path_square_v_grpd A) (@path_square_a_grpd A) (@path_square_b_grpd A)
    (λ box0 : τ (@PathOpenSquareMissingU_grpd A),
      @=
        (@PathOpenSquareMissingU_grpd A)
        (@path_square_restrict_missing_u
          A (@path_open_square_fill_missing_u A box0))
        box0)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ v : τ (@= A x10 x11), λ a : τ (@= A x00 x10),
        λ b : τ (@= A x01 x11),
          @eq_refl
            (@PathOpenSquareMissingU_grpd A)
            (@path_open_square_missing_u_intro
              A x00 x01 x10 x11 v a b))
    box;

symbol path_open_square_missing_v_section
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (@=
      (@PathOpenSquareMissingV_grpd A)
      (@path_square_restrict_missing_v
        A (@path_open_square_fill_missing_v A box))
      box)
≔ @path_open_square_frame_ind
    A (@path_square_u_grpd A) (@path_square_a_grpd A) (@path_square_b_grpd A)
    (λ box0 : τ (@PathOpenSquareMissingV_grpd A),
      @=
        (@PathOpenSquareMissingV_grpd A)
        (@path_square_restrict_missing_v
          A (@path_open_square_fill_missing_v A box0))
        box0)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ u : τ (@= A x00 x01), λ a : τ (@= A x00 x10),
        λ b : τ (@= A x01 x11),
          @eq_refl
            (@PathOpenSquareMissingV_grpd A)
            (@path_open_square_missing_v_intro
              A x00 x01 x10 x11 u a b))
    box;

symbol path_open_square_missing_a_section
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@=
      (@PathOpenSquareMissingA_grpd A)
      (@path_square_restrict_missing_a
        A (@path_open_square_fill_missing_a A box))
      box)
≔ @path_open_square_frame_ind
    A (@path_square_u_grpd A) (@path_square_v_grpd A) (@path_square_b_grpd A)
    (λ box0 : τ (@PathOpenSquareMissingA_grpd A),
      @=
        (@PathOpenSquareMissingA_grpd A)
        (@path_square_restrict_missing_a
          A (@path_open_square_fill_missing_a A box0))
        box0)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ u : τ (@= A x00 x01), λ v : τ (@= A x10 x11),
        λ b : τ (@= A x01 x11),
          @eq_refl
            (@PathOpenSquareMissingA_grpd A)
            (@path_open_square_missing_a_intro
              A x00 x01 x10 x11 u v b))
    box;

symbol path_open_square_missing_b_section
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@=
      (@PathOpenSquareMissingB_grpd A)
      (@path_square_restrict_missing_b
        A (@path_open_square_fill_missing_b A box))
      box)
≔ @path_open_square_frame_ind
    A (@path_square_u_grpd A) (@path_square_v_grpd A) (@path_square_a_grpd A)
    (λ box0 : τ (@PathOpenSquareMissingB_grpd A),
      @=
        (@PathOpenSquareMissingB_grpd A)
        (@path_square_restrict_missing_b
          A (@path_open_square_fill_missing_b A box0))
        box0)
    (λ x00 : τ A, λ x01 : τ A, λ x10 : τ A, λ x11 : τ A,
      λ u : τ (@= A x00 x01), λ v : τ (@= A x10 x11),
        λ a : τ (@= A x00 x10),
          @eq_refl
            (@PathOpenSquareMissingB_grpd A)
            (@path_open_square_missing_b_intro
              A x00 x01 x10 x11 u v a))
    box;
