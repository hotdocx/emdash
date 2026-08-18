/*
  Internal augmented semi-simplex category.

  Objects are finite vertex counts and Homs are path categories of the
  set-classified face codes. Identity delegates to the all-keep code.
  Category composition computes at visible public truncation points and
  routes through the existing face_comp owner; arbitrary composition remains
  at the generic comp_fapp0 head. This narrow boundary avoids the severe
  decision-tree cost measured for an unconstrained category-composition fold.

  The module introduces no functor/transfor action rule, full simplex
  degeneracy, join realization, representable, boundary, horn, or Kan claim.
*/

require open emdash.emdash3_2_semisimplicial_face_codes;

// Augmented semi-simplex category of finite ordinals and injective maps.
injective symbol SemiDeltaPlus_cat : Cat;

rule Obj SemiDeltaPlus_cat
  ↪ Nat_grpd;

rule Hom_cat SemiDeltaPlus_cat $p $n
  ↪ Path_cat (@FaceCode $p $n);

// Identity is the all-keep face code.
rule @id SemiDeltaPlus_cat $n
  ↪ @face_identity $n;

/*
  Visible-point composition beta.

  `trunc_zero` is written on the LHS in its constructor normal form because
  transparent truncation-level aliases normalize before rule selection.
  Retaining p,q,n is a measured subject-reduction guard for the two indexed
  raw-code wrappers. The RHS uses the named public composition owner rather
  than duplicating its structural recursion.
*/
// lhs-audit: keep 2,3,4 -- visible raw-code indices guard subject reduction.
rule @comp_fapp0
      SemiDeltaPlus_cat $p $q $n
      (@trunc_intro
        (trunc_succ (trunc_succ trunc_minus_two))
        (@RawFaceCode $q $n) $g)
      (@trunc_intro
        (trunc_succ (trunc_succ trunc_minus_two))
        (@RawFaceCode $p $q) $f)
  ↪ @face_comp
      $p $q $n
      (@trunc_intro trunc_zero (@RawFaceCode $q $n) $g)
      (@trunc_intro trunc_zero (@RawFaceCode $p $q) $f);

// Every Hom category is the discrete path category of a set of face codes.
symbol semi_delta_plus_hom_is_discrete
  (p n : τ (Obj SemiDeltaPlus_cat))
  : τ (IsDiscreteCat (Hom_cat SemiDeltaPlus_cat p n))
≔ @discrete_cat_intro
    (Path_cat (@FaceCode p n))
    (@face_code_is_set p n)
    (@path_cat_is_groupoidal (@FaceCode p n));
