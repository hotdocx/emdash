/*
  Native variable-dimensional action of semicubical face codes.

  A raw {L,R,*} word is interpreted as a whole restriction functor between
  intrinsic CubicalLevel categories. The recursive result pairs that functor
  with its pseudo-functor property:

    L f |-> action(f) o src
    R f |-> action(f) o tgt
    * f |-> CubicalArrow_func(action(f),is_pseudo(f)).

  The property is essential data for the star branch, not a parallel map.
  Public set-truncated codes are decoded to their curated raw set before this
  recursion, exactly as in variable-dimensional simplex-face realization.
  Every result is a whole functor and therefore retains generic higher action.

  This module adds no face-specific law, Gray comparison, parameterized
  triangular hom, degeneracy, connection, runtime equality, or unifier.
*/

require open emdash.emdash3_2_cubical_levels;
require open emdash.emdash3_2_semicubical_face_codes;

// Whole restriction functor paired with the pseudo property needed to lift it.
symbol CubeFaceActionResult
  (C : Cat)
  (p n : τ Nat_grpd)
  : Grpd
≔ `Σ_ F : τ (Functor
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p)),
    @IsPseudoFunctor
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p)
      F;

symbol cube_face_action_result
  [C : Cat]
  [p n : τ Nat_grpd]
  (F : τ (Functor
    (@CubicalLevel_cat C n)
    (@CubicalLevel_cat C p)))
  (P : τ (@IsPseudoFunctor
    (@CubicalLevel_cat C n)
    (@CubicalLevel_cat C p)
    F))
  : τ (@CubeFaceActionResult C p n)
≔ Struct_sigma F P;

// Structural action on raw words, retaining the property at every recursion step.
injective symbol raw_cube_face_action
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@RawCubeFaceCode p n))
  : τ (@CubeFaceActionResult C p n);

// The empty word acts by identity at level zero.
rule @raw_cube_face_action $C _ _ raw_cube_nil
  ↪ @cube_face_action_result
      $C zero zero
      (@id_func $C)
      (@identity_is_pseudo $C)

// L fixes the new coordinate by source, then applies the older action.
with @raw_cube_face_action $C _ _ (@raw_cube_left $p $n $f)
  ↪ @cube_face_action_result
      $C $p (succ $n)
      (@comp_cat_fapp0
        (@CubicalLevel_cat $C (succ $n))
        (@CubicalLevel_cat $C $n)
        (@CubicalLevel_cat $C $p)
        (sigma_Fst (@raw_cube_face_action $C $p $n $f))
        (@cubical_src_func (@CubicalLevel_cat $C $n)))
      (@comp_is_pseudo
        (@CubicalLevel_cat $C (succ $n))
        (@CubicalLevel_cat $C $n)
        (@CubicalLevel_cat $C $p)
        (@cubical_src_func (@CubicalLevel_cat $C $n))
        (@cubical_src_is_pseudo (@CubicalLevel_cat $C $n))
        (sigma_Fst (@raw_cube_face_action $C $p $n $f))
        (sigma_Snd (@raw_cube_face_action $C $p $n $f)))

// R fixes the new coordinate by target, then applies the older action.
with @raw_cube_face_action $C _ _ (@raw_cube_right $p $n $f)
  ↪ @cube_face_action_result
      $C $p (succ $n)
      (@comp_cat_fapp0
        (@CubicalLevel_cat $C (succ $n))
        (@CubicalLevel_cat $C $n)
        (@CubicalLevel_cat $C $p)
        (sigma_Fst (@raw_cube_face_action $C $p $n $f))
        (@cubical_tgt_func (@CubicalLevel_cat $C $n)))
      (@comp_is_pseudo
        (@CubicalLevel_cat $C (succ $n))
        (@CubicalLevel_cat $C $n)
        (@CubicalLevel_cat $C $p)
        (@cubical_tgt_func (@CubicalLevel_cat $C $n))
        (@cubical_tgt_is_pseudo (@CubicalLevel_cat $C $n))
        (sigma_Fst (@raw_cube_face_action $C $p $n $f))
        (sigma_Snd (@raw_cube_face_action $C $p $n $f)))

// Star preserves the new coordinate by property-carrying CubicalArrow lifting.
with @raw_cube_face_action $C _ _ (@raw_cube_keep $p $n $f)
  ↪ @cube_face_action_result
      $C (succ $p) (succ $n)
      (@CubicalArrow_func
        (@CubicalLevel_cat $C $n)
        (@CubicalLevel_cat $C $p)
        (sigma_Fst (@raw_cube_face_action $C $p $n $f))
        (sigma_Snd (@raw_cube_face_action $C $p $n $f)))
      (@cubical_arrow_is_pseudo
        (@CubicalLevel_cat $C $n)
        (@CubicalLevel_cat $C $p)
        (sigma_Fst (@raw_cube_face_action $C $p $n $f))
        (sigma_Snd (@raw_cube_face_action $C $p $n $f)));

// Curated sethood of finite indexed {L,R,*} words.
constant symbol raw_cube_face_code_is_set
  (p n : τ Nat_grpd)
  : τ (IsSetGrpd (@RawCubeFaceCode p n));

// Decode the public set truncation into its already-set raw syntax.
symbol cube_face_code_raw
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@RawCubeFaceCode p n)
≔ @trunc_rec_ambient
    trunc_zero
    (@RawCubeFaceCode p n)
    (@RawCubeFaceCode p n)
    (@raw_cube_face_code_is_set p n)
    (λ raw : τ (@RawCubeFaceCode p n), raw)
    f;

// Public property-carrying action; visible constructors retain raw computation.
symbol cube_face_action
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@CubeFaceActionResult C p n)
≔ @raw_cube_face_action C p n
    (@cube_face_code_raw p n f);

// Whole restriction functor selected by a public face code.
symbol cube_face_action_func
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (Functor
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
≔ sigma_Fst (@cube_face_action C p n f);

// Pseudo-functor property selected by the same recursion.
symbol cube_face_action_is_pseudo
  [C : Cat]
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@IsPseudoFunctor
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p)
      (@cube_face_action_func C p n f))
≔ sigma_Snd (@cube_face_action C p n f);
