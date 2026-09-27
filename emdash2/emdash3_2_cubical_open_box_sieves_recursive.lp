/*
  Emdash v3.2: variable-dimensional open-box sieves from recursive addresses.

  Boundary membership asks whether some coordinate is fixed. Open-box
  membership follows the same `new-L/new-R/older` recursion as immediate
  faces. For a missing new face, the opposite face is retained and the
  missing/new-star branches recurse into the older boundary. For an older
  missing face, either new face is retained and the star branch recurses into
  the older open box.

  Public membership descends through the existing set truncation. A whole
  higher-sieve owner packages compatibility and yields ordinary sieve
  extension/inclusion and mapping-object restriction at arbitrary dimension.
  This is a variable specification, not a filler theorem.
*/

require open emdash.emdash3_2_cubical_face_addresses;
require open emdash.emdash3_2_path_cubical_open_square_sieves;

// Is a raw face in the proper boundary of its target cube?
injective symbol raw_cube_boundary_member_bool
  [p n : τ Nat_grpd]
  (face : τ (@RawCubeFaceCode p n))
  : τ Bool_grpd;

rule @raw_cube_boundary_member_bool zero zero raw_cube_nil
  ↪ false
with @raw_cube_boundary_member_bool _ _ (@raw_cube_left _ _ _)
  ↪ true
with @raw_cube_boundary_member_bool _ _ (@raw_cube_right _ _ _)
  ↪ true
with @raw_cube_boundary_member_bool _ _ (@raw_cube_keep _ _ $face)
  ↪ @raw_cube_boundary_member_bool _ _ $face;

// Raw open-box membership at one recursively addressed missing face.
injective symbol raw_cube_open_member_bool
  [p n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  (face : τ (@RawCubeFaceCode p (succ n)))
  : τ Bool_grpd;

// Missing new L.
rule @raw_cube_open_member_bool
      _ $n (@raw_cube_face_new_left $n) (@raw_cube_left _ $n $face)
  ↪ @raw_cube_boundary_member_bool _ $n $face
with @raw_cube_open_member_bool
      _ $n (@raw_cube_face_new_left $n) (@raw_cube_right _ $n _)
  ↪ true
with @raw_cube_open_member_bool
      _ $n (@raw_cube_face_new_left $n) (@raw_cube_keep _ $n $face)
  ↪ @raw_cube_boundary_member_bool _ $n $face

// Missing new R.
with @raw_cube_open_member_bool
      _ $n (@raw_cube_face_new_right $n) (@raw_cube_left _ $n _)
  ↪ true
with @raw_cube_open_member_bool
      _ $n (@raw_cube_face_new_right $n) (@raw_cube_right _ $n $face)
  ↪ @raw_cube_boundary_member_bool _ $n $face
with @raw_cube_open_member_bool
      _ $n (@raw_cube_face_new_right $n) (@raw_cube_keep _ $n $face)
  ↪ @raw_cube_boundary_member_bool _ $n $face

// Missing older face: new L/R are retained; star recurses.
with @raw_cube_open_member_bool
      _ (succ $n) (@raw_cube_face_older $n _)
      (@raw_cube_left _ (succ $n) _)
  ↪ true
with @raw_cube_open_member_bool
      _ (succ $n) (@raw_cube_face_older $n _)
      (@raw_cube_right _ (succ $n) _)
  ↪ true
with @raw_cube_open_member_bool
      _ (succ $n) (@raw_cube_face_older $n $missing)
      (@raw_cube_keep _ (succ $n) $face)
  ↪ @raw_cube_open_member_bool _ $n $missing $face;

// Public membership Boolean under set truncation.
symbol cube_open_member_bool
  [p n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  (face : τ (@CubeFaceCode p (succ n)))
  : τ Bool_grpd
≔ @trunc_rec_ambient
    trunc_zero
    (@RawCubeFaceCode p (succ n))
    Bool_grpd
    simplex_bool_is_set
    (λ raw : τ (@RawCubeFaceCode p (succ n)),
      @raw_cube_open_member_bool p n missing raw)
    face;

symbol CubeOpenBoxMember
  [p n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  (face : τ (@CubeFaceCode p (succ n)))
  : Grpd
≔ @simplex_bool_prop (@cube_open_member_bool p n missing face);

symbol cube_open_member_is_prop
  [p n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  (face : τ (@CubeFaceCode p (succ n)))
  : τ (IsPropGrpd (@CubeOpenBoxMember p n missing face))
≔ @simplex_bool_prop_is_prop (@cube_open_member_bool p n missing face);

// Whole variable-dimensional higher-sieve owner.
injective symbol cube_open_higher_sieve
  [n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  : τ (@HigherSieve SemiCubePlus_cat (succ n));

rule @fapp0 _ _ (@cube_open_higher_sieve _ $missing) $q
  ↪ Path_cat
      (@CubeOpenBoxMember
        (@into_restr_domain SemiCubePlus_cat _ $q)
        _
        $missing
        (@into_restr_arrow SemiCubePlus_cat _ $q));

symbol cube_open_ordinary_evidence
  [n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  : τ (@IsOrdinarySieve
      SemiCubePlus_cat (succ n)
      (@cube_open_higher_sieve n missing))
≔ λ q : τ (Obj (@Into_restr_cat SemiCubePlus_cat (succ n))),
    @path_cat_is_subterminal
      (@CubeOpenBoxMember
        (@into_restr_domain SemiCubePlus_cat (succ n) q)
        n
        missing
        (@into_restr_arrow SemiCubePlus_cat (succ n) q))
      (@cube_open_member_is_prop
        (@into_restr_domain SemiCubePlus_cat (succ n) q)
        n
        missing
        (@into_restr_arrow SemiCubePlus_cat (succ n) q));

symbol cube_open_sieve
  [n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  : τ (@Sieve SemiCubePlus_cat (succ n))
≔ @sieve_intro
    SemiCubePlus_cat (succ n)
    (@cube_open_higher_sieve n missing)
    (@cube_open_ordinary_evidence n missing);

symbol cube_open_extension_psh
  [n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  : τ (@Psh SemiCubePlus_cat)
≔ @ordinary_sieve_extension_psh
    SemiCubePlus_cat (succ n)
    (@cube_open_sieve n missing);

symbol cube_open_inclusion
  [n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  : τ (Hom
      (@Psh_cat SemiCubePlus_cat)
      (@cube_open_extension_psh n missing)
      (@StandardSemicube (succ n)))
≔ @ordinary_sieve_extension_inclusion
    SemiCubePlus_cat (succ n)
    (@cube_open_sieve n missing);

// Whole variable-dimensional restriction into the Path semicubical nerve.
symbol path_cube_open_restrict_func
  (A : Grpd)
  [n : τ Nat_grpd]
  (missing : τ (@CubeImmediateFaceAddress (succ n)))
  : τ (Functor
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@StandardSemicube (succ n))
        (@path_semicubical_nerve_func A))
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@cube_open_extension_psh n missing)
        (@path_semicubical_nerve_func A)))
≔ @ordinary_sieve_local_precomp
    SemiCubePlus_cat (succ n)
    (@cube_open_sieve n missing)
    (@path_semicubical_nerve_func A);
