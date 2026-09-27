/*
  Emdash v3.2: four ordinary open-box sieves of the standard two-semicube.

  Raw length-two `{L,R,*}` words decide membership in the union of the three
  retained immediate cofaces. The Boolean observation descends through the
  public set truncation, and one kind-indexed higher-sieve owner packages the
  compatible whole restriction action. Existing ordinary-sieve extension and
  precomposition then give the canonical mapping-object open-box restriction.

  The kind convention is outer L/R = missing u/v and inner L/R = missing a/b.
  This is a fixed dimension-two specification; it introduces no generic
  cofibration algebra, external overlap solver, filler, or Kan theorem.
*/

require open emdash.emdash3_2_path_cubical_nerve;
require open emdash.emdash3_2_simplex2_sieves;

// Observations on the single retained coordinate of a length-one raw code.
injective symbol raw_cube_one_is_fixed
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ zero)))
  : τ Bool_grpd;

rule @raw_cube_one_is_fixed _ (@raw_cube_left _ _ _)
  ↪ true
with @raw_cube_one_is_fixed _ (@raw_cube_right _ _ _)
  ↪ true
with @raw_cube_one_is_fixed _ (@raw_cube_keep _ _ _)
  ↪ false;

injective symbol raw_cube_one_is_left
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ zero)))
  : τ Bool_grpd;

rule @raw_cube_one_is_left _ (@raw_cube_left _ _ _)
  ↪ true
with @raw_cube_one_is_left _ (@raw_cube_right _ _ _)
  ↪ false
with @raw_cube_one_is_left _ (@raw_cube_keep _ _ _)
  ↪ false;

injective symbol raw_cube_one_is_right
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ zero)))
  : τ Bool_grpd;

rule @raw_cube_one_is_right _ (@raw_cube_left _ _ _)
  ↪ false
with @raw_cube_one_is_right _ (@raw_cube_right _ _ _)
  ↪ true
with @raw_cube_one_is_right _ (@raw_cube_keep _ _ _)
  ↪ false;

// Missing outer L/u: retain outer R or either fixed inner face.
injective symbol raw_cube2_missing_u_member_bool
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ (succ zero))))
  : τ Bool_grpd;

rule @raw_cube2_missing_u_member_bool _ (@raw_cube_left _ _ $f)
  ↪ @raw_cube_one_is_fixed _ $f
with @raw_cube2_missing_u_member_bool _ (@raw_cube_right _ _ _)
  ↪ true
with @raw_cube2_missing_u_member_bool _ (@raw_cube_keep _ _ $f)
  ↪ @raw_cube_one_is_fixed _ $f;

// Missing outer R/v: retain outer L or either fixed inner face.
injective symbol raw_cube2_missing_v_member_bool
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ (succ zero))))
  : τ Bool_grpd;

rule @raw_cube2_missing_v_member_bool _ (@raw_cube_left _ _ _)
  ↪ true
with @raw_cube2_missing_v_member_bool _ (@raw_cube_right _ _ $f)
  ↪ @raw_cube_one_is_fixed _ $f
with @raw_cube2_missing_v_member_bool _ (@raw_cube_keep _ _ $f)
  ↪ @raw_cube_one_is_fixed _ $f;

// Missing inner L/a: retain either fixed outer face or inner R.
injective symbol raw_cube2_missing_a_member_bool
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ (succ zero))))
  : τ Bool_grpd;

rule @raw_cube2_missing_a_member_bool _ (@raw_cube_left _ _ _)
  ↪ true
with @raw_cube2_missing_a_member_bool _ (@raw_cube_right _ _ _)
  ↪ true
with @raw_cube2_missing_a_member_bool _ (@raw_cube_keep _ _ $f)
  ↪ @raw_cube_one_is_right _ $f;

// Missing inner R/b: retain either fixed outer face or inner L.
injective symbol raw_cube2_missing_b_member_bool
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ (succ zero))))
  : τ Bool_grpd;

rule @raw_cube2_missing_b_member_bool _ (@raw_cube_left _ _ _)
  ↪ true
with @raw_cube2_missing_b_member_bool _ (@raw_cube_right _ _ _)
  ↪ true
with @raw_cube2_missing_b_member_bool _ (@raw_cube_keep _ _ $f)
  ↪ @raw_cube_one_is_left _ $f;

// The four selected missing-face kinds.
inductive Cube2OpenBoxKindData : TYPE ≔
| cube2_missing_u_kind : Cube2OpenBoxKindData
| cube2_missing_v_kind : Cube2OpenBoxKindData
| cube2_missing_a_kind : Cube2OpenBoxKindData
| cube2_missing_b_kind : Cube2OpenBoxKindData;

injective symbol Cube2OpenBoxKind : Grpd;

rule τ Cube2OpenBoxKind
  ↪ Cube2OpenBoxKindData;

// Kind-indexed raw membership.
injective symbol raw_cube2_open_member_bool
  (kind : τ Cube2OpenBoxKind)
  [p : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p (succ (succ zero))))
  : τ Bool_grpd;

rule @raw_cube2_open_member_bool cube2_missing_u_kind _ $f
  ↪ @raw_cube2_missing_u_member_bool _ $f
with @raw_cube2_open_member_bool cube2_missing_v_kind _ $f
  ↪ @raw_cube2_missing_v_member_bool _ $f
with @raw_cube2_open_member_bool cube2_missing_a_kind _ $f
  ↪ @raw_cube2_missing_a_member_bool _ $f
with @raw_cube2_open_member_bool cube2_missing_b_kind _ $f
  ↪ @raw_cube2_missing_b_member_bool _ $f;

// Public membership Boolean by restricted truncation recursion.
symbol cube2_open_member_bool
  (kind : τ Cube2OpenBoxKind)
  [p : τ Nat_grpd]
  (f : τ (@CubeFaceCode p (succ (succ zero))))
  : τ Bool_grpd
≔ @trunc_rec_ambient
    trunc_zero
    (@RawCubeFaceCode p (succ (succ zero)))
    Bool_grpd
    simplex_bool_is_set
    (λ raw : τ (@RawCubeFaceCode p (succ (succ zero))),
      @raw_cube2_open_member_bool kind p raw)
    f;

symbol Cube2OpenBoxMember
  (kind : τ Cube2OpenBoxKind)
  [p : τ Nat_grpd]
  (f : τ (@CubeFaceCode p (succ (succ zero))))
  : Grpd
≔ @simplex_bool_prop (@cube2_open_member_bool kind p f);

symbol cube2_open_member_is_prop
  (kind : τ Cube2OpenBoxKind)
  [p : τ Nat_grpd]
  (f : τ (@CubeFaceCode p (succ (succ zero))))
  : τ (IsPropGrpd (@Cube2OpenBoxMember kind p f))
≔ @simplex_bool_prop_is_prop (@cube2_open_member_bool kind p f);

// One whole higher-sieve owner retains all compatibility/naturality action.
injective symbol cube2_open_higher_sieve
  (kind : τ Cube2OpenBoxKind)
  : τ (@HigherSieve SemiCubePlus_cat (succ (succ zero)));

rule @fapp0 _ _ (@cube2_open_higher_sieve $kind) $q
  ↪ Path_cat
      (@Cube2OpenBoxMember
        $kind
        (@into_restr_domain SemiCubePlus_cat (succ (succ zero)) $q)
        (@into_restr_arrow SemiCubePlus_cat (succ (succ zero)) $q));

symbol cube2_open_ordinary_evidence
  (kind : τ Cube2OpenBoxKind)
  : τ (@IsOrdinarySieve
      SemiCubePlus_cat
      (succ (succ zero))
      (@cube2_open_higher_sieve kind))
≔ λ q : τ (Obj (@Into_restr_cat
      SemiCubePlus_cat (succ (succ zero)))),
    @path_cat_is_subterminal
      (@Cube2OpenBoxMember
        kind
        (@into_restr_domain SemiCubePlus_cat (succ (succ zero)) q)
        (@into_restr_arrow SemiCubePlus_cat (succ (succ zero)) q))
      (@cube2_open_member_is_prop
        kind
        (@into_restr_domain SemiCubePlus_cat (succ (succ zero)) q)
        (@into_restr_arrow SemiCubePlus_cat (succ (succ zero)) q));

symbol cube2_open_sieve
  (kind : τ Cube2OpenBoxKind)
  : τ (@Sieve SemiCubePlus_cat (succ (succ zero)))
≔ @sieve_intro
    SemiCubePlus_cat
    (succ (succ zero))
    (@cube2_open_higher_sieve kind)
    (@cube2_open_ordinary_evidence kind);

// Whole extension and inclusion into the representable standard two-cube.
symbol cube2_open_extension_psh
  (kind : τ Cube2OpenBoxKind)
  : τ (@Psh SemiCubePlus_cat)
≔ @ordinary_sieve_extension_psh
    SemiCubePlus_cat
    (succ (succ zero))
    (@cube2_open_sieve kind);

symbol cube2_open_inclusion
  (kind : τ Cube2OpenBoxKind)
  : τ (Hom
      (@Psh_cat SemiCubePlus_cat)
      (@cube2_open_extension_psh kind)
      (@StandardSemicube (succ (succ zero))))
≔ @ordinary_sieve_extension_inclusion
    SemiCubePlus_cat
    (succ (succ zero))
    (@cube2_open_sieve kind);

// Canonical whole restriction of complete path-cube maps to compatible boxes.
symbol path_cube2_open_restrict_func
  (A : Grpd)
  (kind : τ Cube2OpenBoxKind)
  : τ (Functor
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@StandardSemicube (succ (succ zero)))
        (@path_semicubical_nerve_func A))
      (Hom_cat
        (@Psh_cat SemiCubePlus_cat)
        (@cube2_open_extension_psh kind)
        (@path_semicubical_nerve_func A)))
≔ @ordinary_sieve_local_precomp
    SemiCubePlus_cat
    (succ (succ zero))
    (@cube2_open_sieve kind)
    (@path_semicubical_nerve_func A);
