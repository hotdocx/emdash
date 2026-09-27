/*
  Emdash v3.2: explicit three-edge carriers for the four open squares.

  One transparent frame stores four vertices followed by three fields whose
  groupoid classifiers may depend on all four vertices. A single
  constructor-complete eliminator owns its decoded nested-Sigma beta. The four
  path open boxes are aliases selecting the retained edge families:

    MissingU = (v,a,b),  MissingV = (u,a,b),
    MissingA = (u,v,b),  MissingB = (u,v,a).

  This avoids four duplicate Sigma theories while keeping every box explicit.
  The module adds no filler, boundary solver, sieve, interval, or unifier.
*/

require open emdash.emdash3_2_path_cubical_nerve;

// The four path-edge classifiers over one square's vertices.
symbol path_square_u_grpd
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  : Grpd
≔ @= A x00 x01;

symbol path_square_v_grpd
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  : Grpd
≔ @= A x10 x11;

symbol path_square_a_grpd
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  : Grpd
≔ @= A x00 x10;

symbol path_square_b_grpd
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  : Grpd
≔ @= A x01 x11;

// Generic explicit three-edge frame.
symbol PathOpenSquareFrame_grpd
  (A : Grpd)
  (E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A,
    Π x10 : τ A,
    Π x11 : τ A,
    Grpd)
  : Grpd
≔ `Σ_ x00 : τ A,
   `Σ_ x01 : τ A,
   `Σ_ x10 : τ A,
   `Σ_ x11 : τ A,
   `Σ_ e0 : τ (E0 x00 x01 x10 x11),
   `Σ_ e1 : τ (E1 x00 x01 x10 x11),
      E2 x00 x01 x10 x11;

symbol path_open_square_frame_intro
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A,
    Π x10 : τ A,
    Π x11 : τ A,
    Grpd]
  (x00 x01 x10 x11 : τ A)
  (e0 : τ (E0 x00 x01 x10 x11))
  (e1 : τ (E1 x00 x01 x10 x11))
  (e2 : τ (E2 x00 x01 x10 x11))
  : τ (@PathOpenSquareFrame_grpd A E0 E1 E2)
≔ Struct_sigma x00
    (Struct_sigma x01
      (Struct_sigma x10
        (Struct_sigma x11
          (Struct_sigma e0
            (Struct_sigma e1 e2)))));

// One eliminator for all explicit three-edge frames.
injective symbol path_open_square_frame_ind
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A,
    Π x10 : τ A,
    Π x11 : τ A,
    Grpd]
  (Q : τ (@PathOpenSquareFrame_grpd A E0 E1 E2) → Grpd)
  (c : Π x00 : τ A,
       Π x01 : τ A,
       Π x10 : τ A,
       Π x11 : τ A,
       Π e0 : τ (E0 x00 x01 x10 x11),
       Π e1 : τ (E1 x00 x01 x10 x11),
       Π e2 : τ (E2 x00 x01 x10 x11),
       τ (Q (@path_open_square_frame_intro
         A E0 E1 E2 x00 x01 x10 x11 e0 e1 e2)))
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ (Q box);

rule @path_open_square_frame_ind
      _ _ _ _ _ $c
      (Struct_sigma $x00
        (Struct_sigma $x01
          (Struct_sigma $x10
            (Struct_sigma $x11
              (Struct_sigma $e0
                (Struct_sigma $e1 $e2))))))
  ↪ $c $x00 $x01 $x10 $x11 $e0 $e1 $e2;

// Shared vertex and retained-field projections.
symbol path_open_square_x00
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A, Π x10 : τ A, Π x11 : τ A, Grpd]
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ A
≔ sigma_Fst box;

symbol path_open_square_x01
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A, Π x10 : τ A, Π x11 : τ A, Grpd]
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ A
≔ sigma_Fst (sigma_Snd box);

symbol path_open_square_x10
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A, Π x10 : τ A, Π x11 : τ A, Grpd]
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ A
≔ sigma_Fst (sigma_Snd (sigma_Snd box));

symbol path_open_square_x11
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A, Π x10 : τ A, Π x11 : τ A, Grpd]
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ A
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd box)));

symbol path_open_square_e0
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A, Π x10 : τ A, Π x11 : τ A, Grpd]
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ (E0
      (@path_open_square_x00 A E0 E1 E2 box)
      (@path_open_square_x01 A E0 E1 E2 box)
      (@path_open_square_x10 A E0 E1 E2 box)
      (@path_open_square_x11 A E0 E1 E2 box))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd box))));

symbol path_open_square_e1
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A, Π x10 : τ A, Π x11 : τ A, Grpd]
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ (E1
      (@path_open_square_x00 A E0 E1 E2 box)
      (@path_open_square_x01 A E0 E1 E2 box)
      (@path_open_square_x10 A E0 E1 E2 box)
      (@path_open_square_x11 A E0 E1 E2 box))
≔ sigma_Fst (sigma_Snd
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd box)))));

symbol path_open_square_e2
  [A : Grpd]
  [E0 E1 E2 : Π x00 : τ A,
    Π x01 : τ A, Π x10 : τ A, Π x11 : τ A, Grpd]
  (box : τ (@PathOpenSquareFrame_grpd A E0 E1 E2))
  : τ (E2
      (@path_open_square_x00 A E0 E1 E2 box)
      (@path_open_square_x01 A E0 E1 E2 box)
      (@path_open_square_x10 A E0 E1 E2 box)
      (@path_open_square_x11 A E0 E1 E2 box))
≔ sigma_Snd (sigma_Snd
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd box)))));

// Four explicit open-square carriers.
symbol PathOpenSquareMissingU_grpd (A : Grpd) : Grpd
≔ @PathOpenSquareFrame_grpd
    A (@path_square_v_grpd A) (@path_square_a_grpd A) (@path_square_b_grpd A);

symbol PathOpenSquareMissingV_grpd (A : Grpd) : Grpd
≔ @PathOpenSquareFrame_grpd
    A (@path_square_u_grpd A) (@path_square_a_grpd A) (@path_square_b_grpd A);

symbol PathOpenSquareMissingA_grpd (A : Grpd) : Grpd
≔ @PathOpenSquareFrame_grpd
    A (@path_square_u_grpd A) (@path_square_v_grpd A) (@path_square_b_grpd A);

symbol PathOpenSquareMissingB_grpd (A : Grpd) : Grpd
≔ @PathOpenSquareFrame_grpd
    A (@path_square_u_grpd A) (@path_square_v_grpd A) (@path_square_a_grpd A);

// Constructor facades retain the semantic edge names.
symbol path_open_square_missing_u_intro
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  : τ (@PathOpenSquareMissingU_grpd A)
≔ @path_open_square_frame_intro
    A (@path_square_v_grpd A) (@path_square_a_grpd A) (@path_square_b_grpd A)
    x00 x01 x10 x11 v a b;

symbol path_open_square_missing_v_intro
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  : τ (@PathOpenSquareMissingV_grpd A)
≔ @path_open_square_frame_intro
    A (@path_square_u_grpd A) (@path_square_a_grpd A) (@path_square_b_grpd A)
    x00 x01 x10 x11 u a b;

symbol path_open_square_missing_a_intro
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (b : τ (@= A x01 x11))
  : τ (@PathOpenSquareMissingA_grpd A)
≔ @path_open_square_frame_intro
    A (@path_square_u_grpd A) (@path_square_v_grpd A) (@path_square_b_grpd A)
    x00 x01 x10 x11 u v b;

symbol path_open_square_missing_b_intro
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  : τ (@PathOpenSquareMissingB_grpd A)
≔ @path_open_square_frame_intro
    A (@path_square_u_grpd A) (@path_square_v_grpd A) (@path_square_a_grpd A)
    x00 x01 x10 x11 u v a;

// Named retained-edge projections.
symbol path_open_square_missing_u_v [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A)) : τ (@path_square_v_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e0 box;

symbol path_open_square_missing_u_a [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A)) : τ (@path_square_a_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e1 box;

symbol path_open_square_missing_u_b [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A)) : τ (@path_square_b_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e2 box;

symbol path_open_square_missing_v_u [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A)) : τ (@path_square_u_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e0 box;

symbol path_open_square_missing_v_a [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A)) : τ (@path_square_a_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e1 box;

symbol path_open_square_missing_v_b [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A)) : τ (@path_square_b_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e2 box;

symbol path_open_square_missing_a_u [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A)) : τ (@path_square_u_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e0 box;

symbol path_open_square_missing_a_v [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A)) : τ (@path_square_v_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e1 box;

symbol path_open_square_missing_a_b [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A)) : τ (@path_square_b_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e2 box;

symbol path_open_square_missing_b_u [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) : τ (@path_square_u_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e0 box;

symbol path_open_square_missing_b_v [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) : τ (@path_square_v_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e1 box;

symbol path_open_square_missing_b_a [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) : τ (@path_square_a_grpd A
    (path_open_square_x00 box) (path_open_square_x01 box)
    (path_open_square_x10 box) (path_open_square_x11 box))
≔ path_open_square_e2 box;
