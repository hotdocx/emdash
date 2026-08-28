/*
  Internal augmented semicube category.

  Objects are cube dimensions and Homs are path categories of the
  set-classified {L,R,*} face codes. Identity delegates to the all-star word.
  Category composition computes at visible public truncation points through
  the existing cube_face_comp owner; arbitrary composition stays at the
  generic comp_fapp0 head.

  This module adds no code recursion, face action, cubical level, degeneracy,
  connection, representable, or Kan claim.
*/

require open emdash.emdash3_2_semicubical_face_codes;

// Augmented semicube category of dimensions and coordinate-face words.
injective symbol SemiCubePlus_cat : Cat;

rule Obj SemiCubePlus_cat
  ↪ Nat_grpd;

rule Hom_cat SemiCubePlus_cat $p $n
  ↪ Path_cat (@CubeFaceCode $p $n);

// Identity is the all-star code.
rule @id SemiCubePlus_cat $n
  ↪ @cube_face_identity $n;

/*
  Visible-point composition beta.

  `trunc_zero` is written in constructor normal form on the LHS because the
  transparent level alias normalizes before rule selection. Retaining p,q,n
  is the measured subject-reduction guard for the indexed raw-code wrappers.
  The RHS delegates to the public composition owner rather than duplicating
  structural substitution.
*/
// lhs-audit: keep 2,3,4 -- visible raw-code indices guard subject reduction.
rule @comp_fapp0
      SemiCubePlus_cat $p $q $n
      (@trunc_intro
        (trunc_succ (trunc_succ trunc_minus_two))
        (@RawCubeFaceCode $q $n) $g)
      (@trunc_intro
        (trunc_succ (trunc_succ trunc_minus_two))
        (@RawCubeFaceCode $p $q) $f)
  ↪ @cube_face_comp
      $p $q $n
      (@trunc_intro trunc_zero (@RawCubeFaceCode $q $n) $g)
      (@trunc_intro trunc_zero (@RawCubeFaceCode $p $q) $f);

// Every Hom is the discrete path category of a set of face codes.
symbol semi_cube_plus_hom_is_discrete
  (p n : τ (Obj SemiCubePlus_cat))
  : τ (IsDiscreteCat (Hom_cat SemiCubePlus_cat p n))
≔ @discrete_cat_intro
    (Path_cat (@CubeFaceCode p n))
    (@cube_face_code_is_set p n)
    (@path_cat_is_groupoidal (@CubeFaceCode p n));
