/* Reviewer example: variable-dimensional open-box sieve recursion. */

require open emdash.emdash3_2_cubical_open_box_sieves_recursive;

// Structural new-face recursion: the missing face keeps only its older
// boundary, while the opposite new face is retained.
assert [p n : τ Nat_grpd]
  (face : τ (@RawCubeFaceCode p n)) ⊢
  @raw_cube_open_member_bool
    p n
    (@raw_cube_face_new_left n)
    (@raw_cube_left p n face)
  ≡ @raw_cube_boundary_member_bool p n face;

assert [p n : τ Nat_grpd]
  (face : τ (@RawCubeFaceCode p n)) ⊢
  @raw_cube_open_member_bool
    p n
    (@raw_cube_face_new_left n)
    (@raw_cube_right p n face)
  ≡ true;

// An older missing face recurses under star and retains both new faces.
assert [p n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  (face : τ (@RawCubeFaceCode p (succ n))) ⊢
  @raw_cube_open_member_bool
    p (succ n)
    (@raw_cube_face_older n missing)
    (@raw_cube_left p (succ n) face)
  ≡ true;

assert [p n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  (face : τ (@RawCubeFaceCode p (succ n))) ⊢
  @raw_cube_open_member_bool
    (succ p) (succ n)
    (@raw_cube_face_older n missing)
    (@raw_cube_keep p (succ n) face)
  ≡ @raw_cube_open_member_bool p n missing face;

// Dimension two recovers the four fixed membership decisions on visible faces.
assert ⊢
  @cube_open_member_bool
    (succ zero) (succ zero)
    cube2_face_address_b
    (@cube_face_address_code (succ zero) cube2_face_address_b)
  ≡ false;

assert ⊢
  @cube_open_member_bool
    (succ zero) (succ zero)
    cube2_face_address_b
    (@cube_face_address_code (succ zero) cube2_face_address_u)
  ≡ true;

// The sieve and whole mapping-object restriction exist at arbitrary dimension.
assert (n : τ Nat_grpd)
  (missing : τ (@CubeImmediateFaceAddress (succ n))) ⊢
  @cube_open_sieve n missing
  : τ (@Sieve SemiCubePlus_cat (succ n));

assert [A : Grpd]
  (n : τ Nat_grpd)
  (missing : τ (@CubeImmediateFaceAddress (succ n))) ⊢
  @path_cube_open_restrict_func A n missing
  : τ (Functor
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@StandardSemicube (succ n))
        (@path_semicubical_nerve_func A))
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@cube_open_extension_psh n missing)
        (@path_semicubical_nerve_func A)));

type @cube_open_member_bool;
type @cube_open_sieve;
type @path_cube_open_restrict_func;
