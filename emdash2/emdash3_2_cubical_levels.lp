/*
  Variable-dimensional intrinsic cubical levels.

  CubicalLevel_cat(C,n) is genuine Nat recursion: level zero is C and every
  successor is CubicalArrow of the preceding level. Objects at levels one,
  two, and three are therefore edges, squares, and cubes, respectively.

  The definition reuses the already-computing CubicalArrow constructor; it is
  not a code-only facade and adds no rule, action, profile, or unifier.
*/

require open emdash.emdash3_2_cubical_square_level;

// Native cubical cell classifier at a variable dimension.
symbol CubicalLevel_cat
  (C : Cat)
  (n : τ Nat_grpd)
  : Cat
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj Cat_cat)
    C
    (λ _ : τ Nat_grpd,
      λ previous : τ (Obj Cat_cat),
        @CubicalArrow_cat previous)
    n;
