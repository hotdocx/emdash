/*
  Computing face-map codes for the augmented semi-simplex category.

  A raw code is a skip/keep word: RawFaceCode(p,n) represents an injective
  monotone map from the p-vertex ordinal to the n-vertex ordinal.  Raw syntax
  owns structural composition.  The public FaceCode(p,n) is its classified
  set truncation, so the later category facade receives intrinsic local
  discreteness without a second observational-equality theory.

  Public constructors and composition remain computational because they use
  the active truncation map and restricted recursor.  This curated indexed
  inductive is standard-library infrastructure; it is not a general
  user-facing inductive-declaration facility and introduces no proof-time
  unification rule.
*/

require open emdash.emdash3_2_truncation_reflector;

// Raw skip/keep syntax indexed by source and target vertex counts.
inductive RawFaceCodeData : nat → nat → TYPE ≔
| raw_face_nil : RawFaceCodeData zero zero
| raw_face_skip p n (f : RawFaceCodeData p n)
    : RawFaceCodeData p (succ n)
| raw_face_keep p n (f : RawFaceCodeData p n)
    : RawFaceCodeData (succ p) (succ n);

// Groupoid/type wrapper exposing the indexed raw syntax to the active kernel.
injective symbol RawFaceCode
  (p n : τ Nat_grpd)
  : Grpd;

rule τ (@RawFaceCode $p $n)
  ↪ RawFaceCodeData $p $n;

/*
  Structural substitution of one skip/keep word into the retained positions
  of another.  The four clauses are exhaustive on well-indexed inputs: the
  empty map, target skip, target keep/source skip, and keep/keep.
*/
injective symbol raw_face_comp
  [p q n : τ Nat_grpd]
  (g : τ (@RawFaceCode q n))
  (f : τ (@RawFaceCode p q))
  : τ (@RawFaceCode p n);

rule @raw_face_comp _ _ _ raw_face_nil raw_face_nil
  ↪ raw_face_nil
with @raw_face_comp _ _ _ (@raw_face_skip _ _ $g) $f
  ↪ @raw_face_skip _ _ (@raw_face_comp _ _ _ $g $f)
with @raw_face_comp _ _ _ (@raw_face_keep _ _ $g) (@raw_face_skip _ _ $f)
  ↪ @raw_face_skip _ _ (@raw_face_comp _ _ _ $g $f)
with @raw_face_comp _ _ _ (@raw_face_keep _ _ $g) (@raw_face_keep _ _ $f)
  ↪ @raw_face_keep _ _ (@raw_face_comp _ _ _ $g $f);

// Public face codes are intrinsically classified as sets.
symbol FaceCode
  (p n : τ Nat_grpd)
  : Grpd
≔ @Trunc_grpd trunc_zero (@RawFaceCode p n);

symbol face_code_is_set
  (p n : τ Nat_grpd)
  : τ (IsSetGrpd (@FaceCode p n))
≔ @trunc_ntype_is_truncated
    trunc_zero
    (@RawFaceCode p n);

// Empty augmented face code.
symbol face_nil
  : τ (@FaceCode zero zero)
≔ @trunc_intro
    trunc_zero
    (@RawFaceCode zero zero)
    raw_face_nil;

// Omit the new last target vertex.
symbol face_skip
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode p n))
  : τ (@FaceCode p (succ n))
≔ @trunc_map
    trunc_zero
    (@RawFaceCode p n)
    (@RawFaceCode p (succ n))
    (λ raw : τ (@RawFaceCode p n),
      @raw_face_skip p n raw)
    f;

// Retain the new last source and target vertices.
symbol face_keep
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode p n))
  : τ (@FaceCode (succ p) (succ n))
≔ @trunc_map
    trunc_zero
    (@RawFaceCode p n)
    (@RawFaceCode (succ p) (succ n))
    (λ raw : τ (@RawFaceCode p n),
      @raw_face_keep p n raw)
    f;

// Identity is the all-keep word, computed by the existing Nat eliminator.
symbol face_identity
  (n : τ Nat_grpd)
  : τ (@FaceCode n n)
≔ @nat_elim
    (λ n0 : τ Nat_grpd, @FaceCode n0 n0)
    face_nil
    (λ n0 : τ Nat_grpd,
      λ previous : τ (@FaceCode n0 n0),
      @face_keep n0 n0 previous)
    n;

/*
  Inner public recursion for a fixed raw outer code.  The codomain is a set,
  so restricted 0-truncation elimination is admissible and computes on every
  visible public constructor.
*/
symbol face_comp_from_raw
  [p q n : τ Nat_grpd]
  (g : τ (@RawFaceCode q n))
  (f : τ (@FaceCode p q))
  : τ (@FaceCode p n)
≔ @trunc_rec_ambient
    trunc_zero
    (@RawFaceCode p q)
    (@FaceCode p n)
    (@face_code_is_set p n)
    (λ raw : τ (@RawFaceCode p q),
      @trunc_intro
        trunc_zero
        (@RawFaceCode p n)
        (@raw_face_comp p q n g raw))
    f;

// Functions into a set form a set, permitting the outer public recursion.
symbol face_code_function_is_set
  [p q n : τ Nat_grpd]
  : τ (IsSetGrpd
      (@Function_grpd (@FaceCode p q) (@FaceCode p n)))
≔ @is_trunc_pi
    trunc_zero
    (@FaceCode p q)
    (λ _ : τ (@FaceCode p q), @FaceCode p n)
    (λ _ : τ (@FaceCode p q), @face_code_is_set p n);

/*
  Public composition.  Both operands are eliminated only into classified
  sets, and visible skip/keep inputs reduce to raw structural composition.
*/
symbol face_comp
  [p q n : τ Nat_grpd]
  (g : τ (@FaceCode q n))
  (f : τ (@FaceCode p q))
  : τ (@FaceCode p n)
≔ (@trunc_rec_ambient
      trunc_zero
      (@RawFaceCode q n)
      (@Function_grpd (@FaceCode p q) (@FaceCode p n))
      (@face_code_function_is_set p q n)
      (λ raw : τ (@RawFaceCode q n),
        λ f0 : τ (@FaceCode p q),
          @face_comp_from_raw p q n raw f0)
      g) f;
