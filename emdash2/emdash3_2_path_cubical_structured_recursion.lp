/*
  Emdash v3.2: Nat-recursive groupoidal cube boundaries, new-left boxes,
  structured filling, and one-way native realization.

  A small internal specification contains a boundary groupoid and a filler
  family. Its cube is their Sigma. Successor boundaries contain two prior
  cubes and equality of their boundaries; the successor filler is the
  corresponding PathOver. This mirrors the recursive cubical boundary/filler
  presentation while remaining an ordinary groupoid construction.

  Every successor has a structured open box missing its new/source face.
  Backward J transport fills that face and gives a reflexive PathOver, with a
  constructor-complete section law. Nat recursion realizes every structured
  cube into the existing native PathCube tower using Sigma-path introduction,
  eq_ap of the preceding realization, and core inclusion.

  Native realization is intentionally one-way. Restricting an arbitrary native
  cube back to the structured carrier still requires inverse realization or
  path-cubical groupoidality closure.
*/

require open emdash.emdash3_2_path_cubical_cube3_open_box;

symbol PathCubeSpecU : Grpd
≔ `Σ_ B : τ Grpd_grpd,
    @Pi_grpd B (λ _ : τ B, Grpd_grpd);

symbol path_cube_spec_boundary
  (S : τ PathCubeSpecU)
  : Grpd
≔ sigma_Fst S;

symbol path_cube_spec_rel
  (S : τ PathCubeSpecU)
  (b : τ (@path_cube_spec_boundary S))
  : Grpd
≔ (sigma_Snd S) b;

symbol path_cube_spec_cube
  (S : τ PathCubeSpecU)
  : Grpd
≔ @Σ_
    (@path_cube_spec_boundary S)
    (λ b : τ (@path_cube_spec_boundary S),
      @path_cube_spec_rel S b);

symbol path_cube_spec_cube_intro
  [S : τ PathCubeSpecU]
  (b : τ (@path_cube_spec_boundary S))
  (r : τ (@path_cube_spec_rel S b))
  : τ (@path_cube_spec_cube S)
≔ @Struct_sigma
    (@path_cube_spec_boundary S)
    (λ b0 : τ (@path_cube_spec_boundary S),
      @path_cube_spec_rel S b0)
    b r;

symbol path_cube_spec_cube_eta
  [S : τ PathCubeSpecU]
  (c : τ (@path_cube_spec_cube S))
  : τ (@=
      (@path_cube_spec_cube S)
      (@path_cube_spec_cube_intro S (sigma_Fst c) (sigma_Snd c))
      c)
≔ @sigma_ind
    (@path_cube_spec_boundary S)
    (λ b : τ (@path_cube_spec_boundary S),
      @path_cube_spec_rel S b)
    (λ c0 : @τΣ_
      (@path_cube_spec_boundary S)
      (λ b : τ (@path_cube_spec_boundary S),
        @path_cube_spec_rel S b),
      @=
        (@path_cube_spec_cube S)
        (@path_cube_spec_cube_intro S (sigma_Fst c0) (sigma_Snd c0))
        c0)
    (λ b : τ (@path_cube_spec_boundary S),
      λ r : τ (@path_cube_spec_rel S b),
        @eq_refl
          (@path_cube_spec_cube S)
          (@path_cube_spec_cube_intro S b r))
    c;

symbol path_cube_spec_base
  (A : Grpd)
  : τ PathCubeSpecU
≔ Struct_sigma
    Unit_grpd
    (λ _ : τ Unit_grpd, A);

symbol path_cube_spec_step_boundary
  (S : τ PathCubeSpecU)
  : Grpd
≔ `Σ_ c0 : τ (@path_cube_spec_cube S),
   `Σ_ c1 : τ (@path_cube_spec_cube S),
      @= (@path_cube_spec_boundary S)
        (sigma_Fst c0) (sigma_Fst c1);

symbol path_cube_spec_step_rel
  (S : τ PathCubeSpecU)
  (b : τ (@path_cube_spec_step_boundary S))
  : Grpd
≔ @PathOver
    (@path_cube_spec_boundary S)
    (λ z : τ (@path_cube_spec_boundary S),
      @path_cube_spec_rel S z)
    (sigma_Fst (sigma_Fst b))
    (sigma_Fst (sigma_Fst (sigma_Snd b)))
    (sigma_Snd (sigma_Snd b))
    (sigma_Snd (sigma_Fst b))
    (sigma_Snd (sigma_Fst (sigma_Snd b)));

symbol path_cube_spec_step_boundary_intro
  [S : τ PathCubeSpecU]
  (c0 c1 : τ (@path_cube_spec_cube S))
  (q : τ (@= (@path_cube_spec_boundary S)
    (sigma_Fst c0) (sigma_Fst c1)))
  : τ (@path_cube_spec_step_boundary S)
≔ @Struct_sigma
    (@path_cube_spec_cube S)
    (λ c00 : τ (@path_cube_spec_cube S),
      `Σ_ c10 : τ (@path_cube_spec_cube S),
        @= (@path_cube_spec_boundary S)
          (sigma_Fst c00) (sigma_Fst c10))
    c0
    (@Struct_sigma
      (@path_cube_spec_cube S)
      (λ c10 : τ (@path_cube_spec_cube S),
        @= (@path_cube_spec_boundary S)
          (sigma_Fst c0) (sigma_Fst c10))
      c1 q);

symbol path_cube_spec_step
  (S : τ PathCubeSpecU)
  : τ PathCubeSpecU
≔ Struct_sigma
    (@path_cube_spec_step_boundary S)
    (λ b : τ (@path_cube_spec_step_boundary S),
      @path_cube_spec_step_rel S b);

symbol path_cube_spec_step_cube_intro
  [S : τ PathCubeSpecU]
  (c0 c1 : τ (@path_cube_spec_cube S))
  (q : τ (@= (@path_cube_spec_boundary S)
    (sigma_Fst c0) (sigma_Fst c1)))
  (top : τ (@PathOver
    (@path_cube_spec_boundary S)
    (λ b : τ (@path_cube_spec_boundary S),
      @path_cube_spec_rel S b)
    (sigma_Fst c0) (sigma_Fst c1) q
    (sigma_Snd c0) (sigma_Snd c1)))
  : τ (@path_cube_spec_cube (@path_cube_spec_step S))
≔ @path_cube_spec_cube_intro
    (@path_cube_spec_step S)
    (@path_cube_spec_step_boundary_intro S c0 c1 q)
    top;

symbol path_cube_spec
  (A : Grpd)
  (n : τ Nat_grpd)
  : τ PathCubeSpecU
≔ @nat_elim
    (λ _ : τ Nat_grpd, PathCubeSpecU)
    (@path_cube_spec_base A)
    (λ _ : τ Nat_grpd,
      λ S : τ PathCubeSpecU,
        @path_cube_spec_step S)
    n;

symbol StructuredPathCubeRec_grpd
  (A : Grpd)
  (n : τ Nat_grpd)
  : Grpd
≔ @path_cube_spec_cube (@path_cube_spec A n);

// Generic open box missing the new/source face of one successor.
symbol StructuredOpenBoxNewLeft_grpd
  (S : τ PathCubeSpecU)
  : Grpd
≔ `Σ_ b0 : τ (@path_cube_spec_boundary S),
   `Σ_ c1 : τ (@path_cube_spec_cube S),
      @= (@path_cube_spec_boundary S) b0 (sigma_Fst c1);

symbol path_structured_open_box_new_left_intro
  [S : τ PathCubeSpecU]
  (b0 : τ (@path_cube_spec_boundary S))
  (c1 : τ (@path_cube_spec_cube S))
  (q : τ (@= (@path_cube_spec_boundary S) b0 (sigma_Fst c1)))
  : τ (@StructuredOpenBoxNewLeft_grpd S)
≔ Struct_sigma b0 (Struct_sigma c1 q);

injective symbol path_structured_open_box_new_left_ind
  [S : τ PathCubeSpecU]
  (Q : τ (@StructuredOpenBoxNewLeft_grpd S) → Grpd)
  (c : Π b0 : τ (@path_cube_spec_boundary S),
       Π c1 : τ (@path_cube_spec_cube S),
       Π q : τ (@= (@path_cube_spec_boundary S) b0 (sigma_Fst c1)),
       τ (Q (@path_structured_open_box_new_left_intro S b0 c1 q)))
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (Q box);

rule @path_structured_open_box_new_left_ind
      _ _ $c (Struct_sigma $b0 (Struct_sigma $c1 $q))
  ↪ $c $b0 $c1 $q;

symbol path_structured_open_box_new_left_b0
  [S : τ PathCubeSpecU]
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (@path_cube_spec_boundary S)
≔ sigma_Fst box;

symbol path_structured_open_box_new_left_c1
  [S : τ PathCubeSpecU]
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (@path_cube_spec_cube S)
≔ sigma_Fst (sigma_Snd box);

symbol path_structured_open_box_new_left_q
  [S : τ PathCubeSpecU]
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (@= (@path_cube_spec_boundary S)
      (@path_structured_open_box_new_left_b0 S box)
      (sigma_Fst (@path_structured_open_box_new_left_c1 S box)))
≔ sigma_Snd (sigma_Snd box);

symbol path_structured_open_box_new_left_hcomp
  [S : τ PathCubeSpecU]
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (@path_cube_spec_rel S
      (@path_structured_open_box_new_left_b0 S box))
≔ @ind_eq
    (@path_cube_spec_boundary S)
    (@path_structured_open_box_new_left_b0 S box)
    (sigma_Fst (@path_structured_open_box_new_left_c1 S box))
    (@path_structured_open_box_new_left_q S box)
    (λ b : τ (@path_cube_spec_boundary S),
      @path_cube_spec_rel S b)
    (sigma_Snd (@path_structured_open_box_new_left_c1 S box));

symbol path_structured_open_box_new_left_top
  [S : τ PathCubeSpecU]
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (@PathOver
      (@path_cube_spec_boundary S)
      (λ b : τ (@path_cube_spec_boundary S),
        @path_cube_spec_rel S b)
      (@path_structured_open_box_new_left_b0 S box)
      (sigma_Fst (@path_structured_open_box_new_left_c1 S box))
      (@path_structured_open_box_new_left_q S box)
      (@path_structured_open_box_new_left_hcomp S box)
      (sigma_Snd (@path_structured_open_box_new_left_c1 S box)))
≔ @eq_refl
    (@path_cube_spec_rel S
      (@path_structured_open_box_new_left_b0 S box))
    (@path_structured_open_box_new_left_hcomp S box);

symbol path_structured_open_box_new_left_fill
  [S : τ PathCubeSpecU]
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (@path_cube_spec_cube (@path_cube_spec_step S))
≔ @path_cube_spec_step_cube_intro
    S
    (@path_cube_spec_cube_intro
      S
      (@path_structured_open_box_new_left_b0 S box)
      (@path_structured_open_box_new_left_hcomp S box))
    (@path_structured_open_box_new_left_c1 S box)
    (@path_structured_open_box_new_left_q S box)
    (@path_structured_open_box_new_left_top S box);

symbol path_structured_open_box_new_left_restrict
  [S : τ PathCubeSpecU]
  (cube : τ (@path_cube_spec_cube (@path_cube_spec_step S)))
  : τ (@StructuredOpenBoxNewLeft_grpd S)
≔ @path_structured_open_box_new_left_intro
    S
    (sigma_Fst (sigma_Fst (sigma_Fst cube)))
    (sigma_Fst (sigma_Snd (sigma_Fst cube)))
    (sigma_Snd (sigma_Snd (sigma_Fst cube)));

symbol path_structured_open_box_new_left_section
  [S : τ PathCubeSpecU]
  (box : τ (@StructuredOpenBoxNewLeft_grpd S))
  : τ (@=
      (@StructuredOpenBoxNewLeft_grpd S)
      (@path_structured_open_box_new_left_restrict S
        (@path_structured_open_box_new_left_fill S box))
      box)
≔ @path_structured_open_box_new_left_ind
    S
    (λ box0 : τ (@StructuredOpenBoxNewLeft_grpd S),
      @=
        (@StructuredOpenBoxNewLeft_grpd S)
        (@path_structured_open_box_new_left_restrict S
          (@path_structured_open_box_new_left_fill S box0))
        box0)
    (λ b0 : τ (@path_cube_spec_boundary S),
      λ c1 : τ (@path_cube_spec_cube S),
        λ q : τ (@= (@path_cube_spec_boundary S) b0 (sigma_Fst c1)),
          @eq_refl
            (@StructuredOpenBoxNewLeft_grpd S)
            (@path_structured_open_box_new_left_intro S b0 c1 q))
    box;

// One successor structured cube canonically determines a path between its
// two predecessor cubes, with Sigma eta restoring arbitrary endpoints.
symbol path_structured_cube_step_path
  [S : τ PathCubeSpecU]
  (z : τ (@path_cube_spec_cube (@path_cube_spec_step S)))
  : τ (@=
      (@path_cube_spec_cube S)
      (sigma_Fst (sigma_Fst z))
      (sigma_Fst (sigma_Snd (sigma_Fst z))))
≔ @eq_trans
    (@path_cube_spec_cube S)
    (sigma_Fst (sigma_Fst z))
    (@path_cube_spec_cube_intro
      S
      (sigma_Fst (sigma_Fst (sigma_Fst z)))
      (sigma_Snd (sigma_Fst (sigma_Fst z))))
    (sigma_Fst (sigma_Snd (sigma_Fst z)))
    (@eq_sym
      (@path_cube_spec_cube S)
      (@path_cube_spec_cube_intro
        S
        (sigma_Fst (sigma_Fst (sigma_Fst z)))
        (sigma_Snd (sigma_Fst (sigma_Fst z))))
      (sigma_Fst (sigma_Fst z))
      (@path_cube_spec_cube_eta S (sigma_Fst (sigma_Fst z))))
    (@eq_trans
      (@path_cube_spec_cube S)
      (@path_cube_spec_cube_intro
        S
        (sigma_Fst (sigma_Fst (sigma_Fst z)))
        (sigma_Snd (sigma_Fst (sigma_Fst z))))
      (@path_cube_spec_cube_intro
        S
        (sigma_Fst (sigma_Fst (sigma_Snd (sigma_Fst z))))
        (sigma_Snd (sigma_Fst (sigma_Snd (sigma_Fst z)))))
      (sigma_Fst (sigma_Snd (sigma_Fst z)))
      (@sigma_path_intro
        (@path_cube_spec_boundary S)
        (λ b : τ (@path_cube_spec_boundary S),
          @path_cube_spec_rel S b)
        (sigma_Fst (sigma_Fst (sigma_Fst z)))
        (sigma_Fst (sigma_Fst (sigma_Snd (sigma_Fst z))))
        (sigma_Snd (sigma_Fst (sigma_Fst z)))
        (sigma_Snd (sigma_Fst (sigma_Snd (sigma_Fst z))))
        (sigma_Snd (sigma_Snd (sigma_Fst z)))
        (sigma_Snd z))
      (@path_cube_spec_cube_eta
        S (sigma_Fst (sigma_Snd (sigma_Fst z)))));

// Nat-recursive realization into the existing native path-cubical tower.
symbol path_structured_path_cube_realize_function
  (A : Grpd)
  (n : τ Nat_grpd)
  : τ (@Function_grpd
      (@StructuredPathCubeRec_grpd A n)
      (@PathCube_grpd A n))
≔ @nat_elim
    (λ n0 : τ Nat_grpd,
      @Function_grpd
        (@StructuredPathCubeRec_grpd A n0)
        (@PathCube_grpd A n0))
    (λ z : τ (@StructuredPathCubeRec_grpd A zero), sigma_Snd z)
    (λ n0 : τ Nat_grpd,
      λ realize : τ (@Function_grpd
        (@StructuredPathCubeRec_grpd A n0)
        (@PathCube_grpd A n0)),
        λ z : τ (@StructuredPathCubeRec_grpd A (succ n0)),
          @path_cube_succ
            A n0
            (realize (sigma_Fst (sigma_Fst z)))
            (realize (sigma_Fst (sigma_Snd (sigma_Fst z))))
            (@path_to_hom
              (@PathCubicalLevel_cat A n0)
              (realize (sigma_Fst (sigma_Fst z)))
              (realize (sigma_Fst (sigma_Snd (sigma_Fst z))))
              (@eq_ap
                (@StructuredPathCubeRec_grpd A n0)
                (@PathCube_grpd A n0)
                realize
                (sigma_Fst (sigma_Fst z))
                (sigma_Fst (sigma_Snd (sigma_Fst z)))
                (@path_structured_cube_step_path
                  (@path_cube_spec A n0) z))))
    n;

symbol path_structured_open_box_new_left_native_fill
  [A : Grpd]
  [n : τ Nat_grpd]
  (box : τ (@StructuredOpenBoxNewLeft_grpd
    (@path_cube_spec A n)))
  : τ (@PathCube_grpd A (succ n))
≔ (@path_structured_path_cube_realize_function A (succ n))
    (@path_structured_open_box_new_left_fill
      (@path_cube_spec A n) box);
