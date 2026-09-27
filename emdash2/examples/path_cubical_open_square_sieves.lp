/* Reviewer example: four ordinary open-box sieves of the standard two-cube. */

require open emdash.emdash3_2_path_cubical_open_square_sieve_realization;

// Each omitted immediate face is absent from its own open box.
assert ⊢
  @cube2_open_member_bool
    cube2_missing_u_kind
    (succ zero)
    (@cube_new_left_face_code (succ zero))
  ≡ false;

assert ⊢
  @cube2_open_member_bool
    cube2_missing_v_kind
    (succ zero)
    (@cube_new_right_face_code (succ zero))
  ≡ false;

assert ⊢
  @cube2_open_member_bool
    cube2_missing_a_kind
    (succ zero)
    (@cube_face_keep
      zero (succ zero)
      (@cube_new_left_face_code zero))
  ≡ false;

assert ⊢
  @cube2_open_member_bool
    cube2_missing_b_kind
    (succ zero)
    (@cube_face_keep
      zero (succ zero)
      (@cube_new_right_face_code zero))
  ≡ false;

// A different immediate face is retained.
assert ⊢
  @cube2_open_member_bool
    cube2_missing_u_kind
    (succ zero)
    (@cube_new_right_face_code (succ zero))
  ≡ true;

assert ⊢
  @cube2_open_member_bool
    cube2_missing_a_kind
    (succ zero)
    (@cube_new_left_face_code (succ zero))
  ≡ true;

// Vertices on the omitted edge remain through intersections with retained faces.
assert ⊢
  @cube2_open_member_bool
    cube2_missing_u_kind
    zero
    (@cube_face_left
      zero (succ zero)
      (@cube_new_left_face_code zero))
  ≡ true;

// The complete identity two-cube is not part of a proper open box.
assert ⊢
  @cube2_open_member_bool
    cube2_missing_b_kind
    (succ (succ zero))
    (@cube_face_identity (succ (succ zero)))
  ≡ false;

// Each kind supplies an ordinary sieve and whole representable inclusion.
assert (kind : τ Cube2OpenBoxKind) ⊢
  @cube2_open_sieve kind
  : τ (@Sieve SemiCubePlus_cat (succ (succ zero)));

assert (kind : τ Cube2OpenBoxKind) ⊢
  @cube2_open_inclusion kind
  : τ (Hom
      (@Psh_cat SemiCubePlus_cat)
      (@cube2_open_extension_psh kind)
      (@StandardSemicube (succ (succ zero))));

// Precomposition is the canonical mapping-object open-box restriction.
assert [A : Grpd]
  (kind : τ Cube2OpenBoxKind) ⊢
  @path_cube2_open_restrict_func A kind
  : τ (Functor
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@StandardSemicube (succ (succ zero)))
        (@path_semicubical_nerve_func A))
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@cube2_open_extension_psh kind)
        (@path_semicubical_nerve_func A)));

// Its next hom action remains generic and whole.
assert [A : Grpd]
  (kind : τ Cube2OpenBoxKind)
  (F G : τ (Hom
    (@Psh_cat SemiCubePlus_cat)
    (@StandardSemicube (succ (succ zero)))
    (@path_semicubical_nerve_func A))) ⊢
  @fapp1_func
    (Hom_cat
      (@Psh_cat SemiCubePlus_cat)
      (@StandardSemicube (succ (succ zero)))
      (@path_semicubical_nerve_func A))
    (Hom_cat
      (@Psh_cat SemiCubePlus_cat)
      (@cube2_open_extension_psh kind)
      (@path_semicubical_nerve_func A))
    (@path_cube2_open_restrict_func A kind)
    F G
  : τ (Functor
      (Hom_cat
        (Hom_cat
          (@Psh_cat SemiCubePlus_cat)
          (@StandardSemicube (succ (succ zero)))
          (@path_semicubical_nerve_func A))
        F G)
      (Hom_cat
        (Hom_cat
          (@Psh_cat SemiCubePlus_cat)
          (@cube2_open_extension_psh kind)
          (@path_semicubical_nerve_func A))
        (@fapp0 _ _ (@path_cube2_open_restrict_func A kind) F)
        (@fapp0 _ _ (@path_cube2_open_restrict_func A kind) G)));

type @cube2_open_sieve;
type @path_cube2_open_restrict_func;

// Explicit boxes realize as compatible whole maps from the matching sieve.
assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) ⊢
  @path_open_square_sieve_map_missing_b A box
  : τ (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_b_kind));

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A)) ⊢
  @path_open_square_sieve_map_missing_u A box
  : τ (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_u_kind));

// The representative realization retains higher equality action.
assert [A : Grpd] ⊢
  @path_open_square_sieve_map_missing_b_func A
  : τ (Functor
      (Path_cat (@PathOpenSquareMissingB_grpd A))
      (Path_cat (Obj (@PathCube2OpenBoxMap_cat A cube2_missing_b_kind))));

type @path_open_square_sieve_map_missing_b;
