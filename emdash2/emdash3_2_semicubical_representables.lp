/*
  Emdash v3.2: standard representable semicubes and their native decoding.

  The standard n-semicube is the Yoneda representable of the internal
  augmented semicube category.  Its p-level is therefore

    Hom_SemiCubePlus(p,n) = Path_cat(CubeFaceCode(p,n)).

  The Hom action of the existing whole semicubical nerve decodes that entire
  representable level to native restriction functors

    CubicalLevel(C,n) -> CubicalLevel(C,p).

  The existing nerve-action path compares every decoded object with the
  computing profile-retaining {L,R,*} interpreter, while generic fapp1 keeps
  higher representable paths iterable.  This module adds no face syntax,
  dimension-specific boundary, rule, unifier, degeneracy, connection, or Kan
  claim.
*/

require open emdash.emdash3_2_semicubical_nerve;
require open emdash.emdash3_2_presheaves;

// Standard representable n-semicube: Hom(-,n).
symbol StandardSemicube
  (n : τ (Obj SemiCubePlus_cat))
  : τ (@Psh SemiCubePlus_cat)
≔ @yoneda_psh SemiCubePlus_cat n;

// Its p-level is the path category of public p -> n face codes.
symbol standard_semicube_level
  (n p : τ (Obj SemiCubePlus_cat))
  : Cat
≔ @fapp0
    (Op_cat SemiCubePlus_cat)
    Cat_cat
    (@StandardSemicube n)
    p;

// Whole decoder from representable faces to native restriction functors.
symbol standard_semicube_native_decode_func
  [C : Cat]
  (p n : τ (Obj SemiCubePlus_cat))
  : τ (Functor
      (@standard_semicube_level n p)
      (Functor_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p)))
≔ @fapp1_func
    (Op_cat SemiCubePlus_cat)
    Cat_cat
    (@semicubical_nerve_func C)
    n p;

// Named selected comparison with the computing {L,R,*} interpreter.
symbol standard_semicube_native_decode_path
  [C : Cat]
  [p n : τ (Obj SemiCubePlus_cat)]
  (f : τ (@CubeFaceCode p n))
  : τ (@=
      (Hom Cat_cat
        (@CubicalLevel_cat C n)
        (@CubicalLevel_cat C p))
      (@fapp0
        (@standard_semicube_level n p)
        (Functor_cat
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C p))
        (@standard_semicube_native_decode_func C p n)
        f)
      (@cube_face_action_func C p n f))
≔ @semicubical_nerve_action_path C n p f;

// Higher representable action remains the generic Hom action of the decoder.
symbol standard_semicube_native_decode_hom_func
  [C : Cat]
  [p n : τ (Obj SemiCubePlus_cat)]
  (f g : τ (@CubeFaceCode p n))
  : τ (Functor
      (Hom_cat (@standard_semicube_level n p) f g)
      (Hom_cat
        (Functor_cat
          (@CubicalLevel_cat C n)
          (@CubicalLevel_cat C p))
        (@fapp0
          (@standard_semicube_level n p)
          (Functor_cat
            (@CubicalLevel_cat C n)
            (@CubicalLevel_cat C p))
          (@standard_semicube_native_decode_func C p n)
          f)
        (@fapp0
          (@standard_semicube_level n p)
          (Functor_cat
            (@CubicalLevel_cat C n)
            (@CubicalLevel_cat C p))
          (@standard_semicube_native_decode_func C p n)
          g)))
≔ @fapp1_func
    (@standard_semicube_level n p)
    (Functor_cat
      (@CubicalLevel_cat C n)
      (@CubicalLevel_cat C p))
    (@standard_semicube_native_decode_func C p n)
    f g;
