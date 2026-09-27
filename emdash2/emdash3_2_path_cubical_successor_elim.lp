/*
  Emdash v3.2: one eliminator for every derived successor cube carrier.

  PathCube(A,succ n) is the decoded nested-Sigma carrier of arrows in
  PathCubicalLevel(A,n). The selected constructor is therefore

    path_cube_succ(X,Y,theta) = (X,(Y,theta)).

  This module exposes one Nat-generic dependent eliminator, its constructor
  beta, the three canonical projections, and propositional constructor eta.
  It is a facade over the already-decoded Sigma carrier, not a primitive cube
  grammar. The single rule is warning-neutral at its owner position and has no
  inferred-LHS candidate.
*/

require open emdash.emdash3_2_path_cubical_levels;

// Dependent elimination for a successor cube's source, target, and top cell.
injective symbol path_cube_succ_ind
  [A : Grpd]
  [n : τ Nat_grpd]
  (Q : τ (@PathCube_grpd A (succ n)) → Grpd)
  (c : Π X : τ (@PathCube_grpd A n),
       Π Y : τ (@PathCube_grpd A n),
       Π theta : τ (Hom (@PathCubicalLevel_cat A n) X Y),
       τ (Q (@path_cube_succ A n X Y theta)))
  (Z : τ (@PathCube_grpd A (succ n)))
  : τ (Q Z);

// Constructor beta for the decoded nested-Sigma carrier.
rule @path_cube_succ_ind
      _ _ _ $c
      (Struct_sigma $X (Struct_sigma $Y $theta))
  ↪ $c $X $Y $theta;

// Canonical source, target, and top-cell observations.
symbol path_cube_succ_src
  [A : Grpd]
  [n : τ Nat_grpd]
  (Z : τ (@PathCube_grpd A (succ n)))
  : τ (@PathCube_grpd A n)
≔ sigma_Fst Z;

symbol path_cube_succ_tgt
  [A : Grpd]
  [n : τ Nat_grpd]
  (Z : τ (@PathCube_grpd A (succ n)))
  : τ (@PathCube_grpd A n)
≔ sigma_Fst (sigma_Snd Z);

symbol path_cube_succ_cell
  [A : Grpd]
  [n : τ Nat_grpd]
  (Z : τ (@PathCube_grpd A (succ n)))
  : τ (Hom
      (@PathCubicalLevel_cat A n)
      (@path_cube_succ_src A n Z)
      (@path_cube_succ_tgt A n Z))
≔ sigma_Snd (sigma_Snd Z);

// Every successor cube is propositionally its constructor reconstruction.
symbol path_cube_succ_eta
  [A : Grpd]
  [n : τ Nat_grpd]
  (Z : τ (@PathCube_grpd A (succ n)))
  : τ (@=
      (@PathCube_grpd A (succ n))
      (@path_cube_succ
        A n
        (@path_cube_succ_src A n Z)
        (@path_cube_succ_tgt A n Z)
        (@path_cube_succ_cell A n Z))
      Z)
≔ @path_cube_succ_ind
    A n
    (λ Z0 : τ (@PathCube_grpd A (succ n)),
      @=
        (@PathCube_grpd A (succ n))
        (@path_cube_succ
          A n
          (sigma_Fst Z0)
          (sigma_Fst (sigma_Snd Z0))
          (sigma_Snd (sigma_Snd Z0)))
        Z0)
    (λ X : τ (@PathCube_grpd A n),
      λ Y : τ (@PathCube_grpd A n),
        λ theta : τ (Hom (@PathCubicalLevel_cat A n) X Y),
          @eq_refl
            (@PathCube_grpd A (succ n))
            (@path_cube_succ A n X Y theta))
    Z;
