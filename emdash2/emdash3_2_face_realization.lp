/*
  Variable-dimension realization of nonempty semisimplex face codes.

  Raw skip/keep syntax computes recursively into whole functors between the
  join-built directed simplex shapes:

    skip f  |-> join_fst o realize(f)
    keep f  |-> join_map(realize(f),id_1).

  RawFaceCode is the curated indexed syntax of finite monotone injections, so
  this extension records its standard sethood property. Existing restricted
  0-truncation recursion then decodes public FaceCode values back to raw normal
  forms and preserves the visible constructor computations.

  This module does not yet assemble a functor from SemiDeltaPlus_cat to
  Cat_cat. Realization of the all-keep code stops at join_map(id,id), and the
  first new-vertex composition stops at generic join-map composition. Those
  whole identity/composition comparisons require the scoped join uniqueness
  boundary isolated by the join-mapping-recursion module. No local fold or
  proof-time unifier is added here, and generic strict-profile evidence remains
  a later profile question.
*/

require open emdash.emdash3_2_join_mapping_recursion;

// Curated sethood of the finite indexed skip/keep syntax. A future direct
// no-confusion proof may replace this evidence constant without changing the
// public face-realization computation.
constant symbol raw_face_code_is_set
  (p n : τ Nat_grpd)
  : τ (IsSetGrpd (@RawFaceCode p n));

// Decode the public set truncation into its already-set raw syntax.
symbol face_code_raw
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode p n))
  : τ (@RawFaceCode p n)
≔ @trunc_rec_ambient
    trunc_zero
    (@RawFaceCode p n)
    (@RawFaceCode p n)
    (@raw_face_code_is_set p n)
    (λ raw : τ (@RawFaceCode p n), raw)
    f;

// Recursive realization for nonempty raw source and target ordinals.
injective symbol raw_face_realize_func
  [p n : τ Nat_grpd]
  (f : τ (@RawFaceCode (succ p) (succ n)))
  : τ (Functor
      (@DirectedSimplex_cat p)
      (@DirectedSimplex_cat n));

// The unique one-vertex identity.
rule @raw_face_realize_func _ _
      (@raw_face_keep zero zero raw_face_nil)
  ↪ @id_func Terminal_cat;

// Skipping the new target vertex factors through the left join inclusion.
rule @raw_face_realize_func _ _
      (@raw_face_skip (succ $p) (succ $n) $f)
  ↪ @comp_cat_fapp0
      (@DirectedSimplex_cat $p)
      (@DirectedSimplex_cat $n)
      (@DirectedSimplex_cat (succ $n))
      (@join_fst_func (@DirectedSimplex_cat $n) Terminal_cat)
      (@raw_face_realize_func $p $n $f);

// Retaining the final vertex recursively maps both join branches.
rule @raw_face_realize_func _ _
      (@raw_face_keep (succ $p) (succ $n) $f)
  ↪ @join_map_func
      (@DirectedSimplex_cat $p)
      Terminal_cat
      (@DirectedSimplex_cat $n)
      Terminal_cat
      (@raw_face_realize_func $p $n $f)
      (@id_func Terminal_cat);

// A one-vertex face retaining the final target is the right inclusion. The
// empty-source predecessor is unique and need not be inspected.
rule @raw_face_realize_func _ _
      (@raw_face_keep zero (succ $n) _)
  ↪ @join_snd_func (@DirectedSimplex_cat $n) Terminal_cat;

// Public realization. Visible trunc_intro/skip/keep inputs retain the raw
// recursive computations through face_code_raw.
symbol face_realize_func
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode (succ p) (succ n)))
  : τ (Functor
      (@DirectedSimplex_cat p)
      (@DirectedSimplex_cat n))
≔ @raw_face_realize_func p n
    (@face_code_raw (succ p) (succ n) f);
