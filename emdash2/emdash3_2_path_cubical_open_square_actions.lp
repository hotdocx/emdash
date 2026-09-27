/*
  Emdash v3.2: whole Path-map action of open-square restriction and filling.

  Raw restriction/filler functions lift through the existing `path_map_func`.
  The four pointwise section laws assemble by `PiFunext`; `path_map_transf`
  retains their equality-valued whole action. No native directed-Hom functor,
  cubical naturality record, or new computation rule is introduced.
*/

require open emdash.emdash3_2_path_cubical_open_square_sections;

// Raw filler functions.
symbol path_open_square_fill_missing_u_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathOpenSquareMissingU_grpd A)
      (@PathCube_grpd A (succ (succ zero))))
≔ λ box : τ (@PathOpenSquareMissingU_grpd A),
    @path_open_square_fill_missing_u A box;

symbol path_open_square_fill_missing_v_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathOpenSquareMissingV_grpd A)
      (@PathCube_grpd A (succ (succ zero))))
≔ λ box : τ (@PathOpenSquareMissingV_grpd A),
    @path_open_square_fill_missing_v A box;

symbol path_open_square_fill_missing_a_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathOpenSquareMissingA_grpd A)
      (@PathCube_grpd A (succ (succ zero))))
≔ λ box : τ (@PathOpenSquareMissingA_grpd A),
    @path_open_square_fill_missing_a A box;

symbol path_open_square_fill_missing_b_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathOpenSquareMissingB_grpd A)
      (@PathCube_grpd A (succ (succ zero))))
≔ λ box : τ (@PathOpenSquareMissingB_grpd A),
    @path_open_square_fill_missing_b A box;

// Whole Path-map filler functors.
symbol path_open_square_fill_missing_u_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathOpenSquareMissingU_grpd A))
      (Path_cat (@PathCube_grpd A (succ (succ zero)))))
≔ @path_map_func
    (@PathOpenSquareMissingU_grpd A)
    (@PathCube_grpd A (succ (succ zero)))
    (@path_open_square_fill_missing_u_function A);

symbol path_open_square_fill_missing_v_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathOpenSquareMissingV_grpd A))
      (Path_cat (@PathCube_grpd A (succ (succ zero)))))
≔ @path_map_func
    (@PathOpenSquareMissingV_grpd A)
    (@PathCube_grpd A (succ (succ zero)))
    (@path_open_square_fill_missing_v_function A);

symbol path_open_square_fill_missing_a_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathOpenSquareMissingA_grpd A))
      (Path_cat (@PathCube_grpd A (succ (succ zero)))))
≔ @path_map_func
    (@PathOpenSquareMissingA_grpd A)
    (@PathCube_grpd A (succ (succ zero)))
    (@path_open_square_fill_missing_a_function A);

symbol path_open_square_fill_missing_b_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathOpenSquareMissingB_grpd A))
      (Path_cat (@PathCube_grpd A (succ (succ zero)))))
≔ @path_map_func
    (@PathOpenSquareMissingB_grpd A)
    (@PathCube_grpd A (succ (succ zero)))
    (@path_open_square_fill_missing_b_function A);

// Whole Path-map restriction functors.
symbol path_square_restrict_missing_u_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathCube_grpd A (succ (succ zero))))
      (Path_cat (@PathOpenSquareMissingU_grpd A)))
≔ @path_map_func
    (@PathCube_grpd A (succ (succ zero)))
    (@PathOpenSquareMissingU_grpd A)
    (@path_square_restrict_missing_u_function A);

symbol path_square_restrict_missing_v_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathCube_grpd A (succ (succ zero))))
      (Path_cat (@PathOpenSquareMissingV_grpd A)))
≔ @path_map_func
    (@PathCube_grpd A (succ (succ zero)))
    (@PathOpenSquareMissingV_grpd A)
    (@path_square_restrict_missing_v_function A);

symbol path_square_restrict_missing_a_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathCube_grpd A (succ (succ zero))))
      (Path_cat (@PathOpenSquareMissingA_grpd A)))
≔ @path_map_func
    (@PathCube_grpd A (succ (succ zero)))
    (@PathOpenSquareMissingA_grpd A)
    (@path_square_restrict_missing_a_function A);

symbol path_square_restrict_missing_b_func (A : Grpd)
  : τ (Functor
      (Path_cat (@PathCube_grpd A (succ (succ zero))))
      (Path_cat (@PathOpenSquareMissingB_grpd A)))
≔ @path_map_func
    (@PathCube_grpd A (succ (succ zero)))
    (@PathOpenSquareMissingB_grpd A)
    (@path_square_restrict_missing_b_function A);

// Whole function paths for the four algebraic sections.
symbol path_open_square_missing_u_section_function_path (A : Grpd)
  : τ (@=
      (@Function_grpd
        (@PathOpenSquareMissingU_grpd A)
        (@PathOpenSquareMissingU_grpd A))
      (λ box : τ (@PathOpenSquareMissingU_grpd A),
        @path_square_restrict_missing_u
          A (@path_open_square_fill_missing_u A box))
      (λ box : τ (@PathOpenSquareMissingU_grpd A), box))
≔ @PiFunext
    (@PathOpenSquareMissingU_grpd A)
    (λ _ : τ (@PathOpenSquareMissingU_grpd A),
      @PathOpenSquareMissingU_grpd A)
    (λ box : τ (@PathOpenSquareMissingU_grpd A),
      @path_square_restrict_missing_u
        A (@path_open_square_fill_missing_u A box))
    (λ box : τ (@PathOpenSquareMissingU_grpd A), box)
    (λ box : τ (@PathOpenSquareMissingU_grpd A),
      @path_open_square_missing_u_section A box);

symbol path_open_square_missing_v_section_function_path (A : Grpd)
  : τ (@=
      (@Function_grpd
        (@PathOpenSquareMissingV_grpd A)
        (@PathOpenSquareMissingV_grpd A))
      (λ box : τ (@PathOpenSquareMissingV_grpd A),
        @path_square_restrict_missing_v
          A (@path_open_square_fill_missing_v A box))
      (λ box : τ (@PathOpenSquareMissingV_grpd A), box))
≔ @PiFunext
    (@PathOpenSquareMissingV_grpd A)
    (λ _ : τ (@PathOpenSquareMissingV_grpd A),
      @PathOpenSquareMissingV_grpd A)
    (λ box : τ (@PathOpenSquareMissingV_grpd A),
      @path_square_restrict_missing_v
        A (@path_open_square_fill_missing_v A box))
    (λ box : τ (@PathOpenSquareMissingV_grpd A), box)
    (λ box : τ (@PathOpenSquareMissingV_grpd A),
      @path_open_square_missing_v_section A box);

symbol path_open_square_missing_a_section_function_path (A : Grpd)
  : τ (@=
      (@Function_grpd
        (@PathOpenSquareMissingA_grpd A)
        (@PathOpenSquareMissingA_grpd A))
      (λ box : τ (@PathOpenSquareMissingA_grpd A),
        @path_square_restrict_missing_a
          A (@path_open_square_fill_missing_a A box))
      (λ box : τ (@PathOpenSquareMissingA_grpd A), box))
≔ @PiFunext
    (@PathOpenSquareMissingA_grpd A)
    (λ _ : τ (@PathOpenSquareMissingA_grpd A),
      @PathOpenSquareMissingA_grpd A)
    (λ box : τ (@PathOpenSquareMissingA_grpd A),
      @path_square_restrict_missing_a
        A (@path_open_square_fill_missing_a A box))
    (λ box : τ (@PathOpenSquareMissingA_grpd A), box)
    (λ box : τ (@PathOpenSquareMissingA_grpd A),
      @path_open_square_missing_a_section A box);

symbol path_open_square_missing_b_section_function_path (A : Grpd)
  : τ (@=
      (@Function_grpd
        (@PathOpenSquareMissingB_grpd A)
        (@PathOpenSquareMissingB_grpd A))
      (λ box : τ (@PathOpenSquareMissingB_grpd A),
        @path_square_restrict_missing_b
          A (@path_open_square_fill_missing_b A box))
      (λ box : τ (@PathOpenSquareMissingB_grpd A), box))
≔ @PiFunext
    (@PathOpenSquareMissingB_grpd A)
    (λ _ : τ (@PathOpenSquareMissingB_grpd A),
      @PathOpenSquareMissingB_grpd A)
    (λ box : τ (@PathOpenSquareMissingB_grpd A),
      @path_square_restrict_missing_b
        A (@path_open_square_fill_missing_b A box))
    (λ box : τ (@PathOpenSquareMissingB_grpd A), box)
    (λ box : τ (@PathOpenSquareMissingB_grpd A),
      @path_open_square_missing_b_section A box);

// Equality-valued whole action of one representative section law.
symbol path_open_square_missing_b_section_transf (A : Grpd)
  : τ (Transf
      (@path_map_func
        (@PathOpenSquareMissingB_grpd A)
        (@PathOpenSquareMissingB_grpd A)
        (λ box : τ (@PathOpenSquareMissingB_grpd A),
          @path_square_restrict_missing_b
            A (@path_open_square_fill_missing_b A box)))
      (@path_map_func
        (@PathOpenSquareMissingB_grpd A)
        (@PathOpenSquareMissingB_grpd A)
        (λ box : τ (@PathOpenSquareMissingB_grpd A), box)))
≔ @path_map_transf
    (@PathOpenSquareMissingB_grpd A)
    (@PathOpenSquareMissingB_grpd A)
    (λ box : τ (@PathOpenSquareMissingB_grpd A),
      @path_square_restrict_missing_b
        A (@path_open_square_fill_missing_b A box))
    (λ box : τ (@PathOpenSquareMissingB_grpd A), box)
    (@path_open_square_missing_b_section_function_path A);

// First retained hom action of a representative filler.
symbol path_open_square_fill_missing_b_hom_func
  [A : Grpd]
  (X Y : τ (@PathOpenSquareMissingB_grpd A))
  : τ (Functor
      (Path_cat (@= (@PathOpenSquareMissingB_grpd A) X Y))
      (Path_cat (@=
        (@PathCube_grpd A (succ (succ zero)))
        (@path_open_square_fill_missing_b A X)
        (@path_open_square_fill_missing_b A Y))))
≔ @fapp1_func
    (Path_cat (@PathOpenSquareMissingB_grpd A))
    (Path_cat (@PathCube_grpd A (succ (succ zero))))
    (@path_open_square_fill_missing_b_func A)
    X Y;
