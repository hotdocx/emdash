/*
  Computing face-map codes for the augmented semicube category.

  RawCubeFaceCode(p,n) is a length-n word in {L,R,*} with exactly p stars.
  L and R fix a coordinate at its two endpoints; * retains a source
  coordinate. Raw syntax owns structural substitution into the retained star
  positions of an outer word.

  The public CubeFaceCode(p,n) is the classified set truncation of that raw
  syntax. Visible constructors, identities, and composition still compute
  through the active restricted recursor. This is curated standard-library
  infrastructure, not a general inductive-declaration facility, and it adds
  no proof-time unifier.
*/

require open emdash.emdash3_2_truncation_reflector;

// Intrinsically indexed raw {L,R,*} syntax.
inductive RawCubeFaceCodeData : nat → nat → TYPE ≔
| raw_cube_nil : RawCubeFaceCodeData zero zero
| raw_cube_left p n (f : RawCubeFaceCodeData p n)
    : RawCubeFaceCodeData p (succ n)
| raw_cube_right p n (f : RawCubeFaceCodeData p n)
    : RawCubeFaceCodeData p (succ n)
| raw_cube_keep p n (f : RawCubeFaceCodeData p n)
    : RawCubeFaceCodeData (succ p) (succ n);

// Groupoid/type wrapper exposing the indexed raw syntax to the active kernel.
injective symbol RawCubeFaceCode
  (p n : τ Nat_grpd)
  : Grpd;

rule τ (@RawCubeFaceCode $p $n)
  ↪ RawCubeFaceCodeData $p $n;

/*
  Structural substitution into the star positions of the outer word.

  Outer L/R pass through without consuming the inner code. Outer * consumes
  one inner constructor and emits its {L,R,*} choice. These six clauses are
  exhaustive on well-indexed inputs.
*/
injective symbol raw_cube_comp
  [p q n : τ Nat_grpd]
  (g : τ (@RawCubeFaceCode q n))
  (f : τ (@RawCubeFaceCode p q))
  : τ (@RawCubeFaceCode p n);

rule @raw_cube_comp _ _ _ raw_cube_nil raw_cube_nil
  ↪ raw_cube_nil
with @raw_cube_comp _ _ _ (@raw_cube_left _ _ $g) $f
  ↪ @raw_cube_left _ _ (@raw_cube_comp _ _ _ $g $f)
with @raw_cube_comp _ _ _ (@raw_cube_right _ _ $g) $f
  ↪ @raw_cube_right _ _ (@raw_cube_comp _ _ _ $g $f)
with @raw_cube_comp _ _ _ (@raw_cube_keep _ _ $g) (@raw_cube_left _ _ $f)
  ↪ @raw_cube_left _ _ (@raw_cube_comp _ _ _ $g $f)
with @raw_cube_comp _ _ _ (@raw_cube_keep _ _ $g) (@raw_cube_right _ _ $f)
  ↪ @raw_cube_right _ _ (@raw_cube_comp _ _ _ $g $f)
with @raw_cube_comp _ _ _ (@raw_cube_keep _ _ $g) (@raw_cube_keep _ _ $f)
  ↪ @raw_cube_keep _ _ (@raw_cube_comp _ _ _ $g $f);

// Public semicubical face codes are intrinsically classified as sets.
symbol CubeFaceCode
  (p n : τ Nat_grpd)
  : Grpd
≔ @Trunc_grpd trunc_zero (@RawCubeFaceCode p n);

symbol cube_face_code_is_set
  (p n : τ Nat_grpd)
  : τ (IsSetGrpd (@CubeFaceCode p n))
≔ @trunc_ntype_is_truncated
    trunc_zero
    (@RawCubeFaceCode p n);

// Empty augmented cube-face code.
symbol cube_face_nil
  : τ (@CubeFaceCode zero zero)
≔ @trunc_intro
    trunc_zero
    (@RawCubeFaceCode zero zero)
    raw_cube_nil;

// Fix the new target coordinate at its left endpoint.
symbol cube_face_left
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@CubeFaceCode p (succ n))
≔ @trunc_map
    trunc_zero
    (@RawCubeFaceCode p n)
    (@RawCubeFaceCode p (succ n))
    (λ raw : τ (@RawCubeFaceCode p n),
      @raw_cube_left p n raw)
    f;

// Fix the new target coordinate at its right endpoint.
symbol cube_face_right
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@CubeFaceCode p (succ n))
≔ @trunc_map
    trunc_zero
    (@RawCubeFaceCode p n)
    (@RawCubeFaceCode p (succ n))
    (λ raw : τ (@RawCubeFaceCode p n),
      @raw_cube_right p n raw)
    f;

// Retain the new source coordinate as the new target coordinate.
symbol cube_face_keep
  [p n : τ Nat_grpd]
  (f : τ (@CubeFaceCode p n))
  : τ (@CubeFaceCode (succ p) (succ n))
≔ @trunc_map
    trunc_zero
    (@RawCubeFaceCode p n)
    (@RawCubeFaceCode (succ p) (succ n))
    (λ raw : τ (@RawCubeFaceCode p n),
      @raw_cube_keep p n raw)
    f;

// Identity is the all-star word.
symbol cube_face_identity
  (n : τ Nat_grpd)
  : τ (@CubeFaceCode n n)
≔ @nat_elim
    (λ n0 : τ Nat_grpd, @CubeFaceCode n0 n0)
    cube_face_nil
    (λ n0 : τ Nat_grpd,
      λ previous : τ (@CubeFaceCode n0 n0),
      @cube_face_keep n0 n0 previous)
    n;

/*
  Inner public recursion for a fixed raw outer code. The codomain is a set,
  so restricted 0-truncation elimination is admissible and computes on every
  visible public constructor.
*/
symbol cube_face_comp_from_raw
  [p q n : τ Nat_grpd]
  (g : τ (@RawCubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@CubeFaceCode p n)
≔ @trunc_rec_ambient
    trunc_zero
    (@RawCubeFaceCode p q)
    (@CubeFaceCode p n)
    (@cube_face_code_is_set p n)
    (λ raw : τ (@RawCubeFaceCode p q),
      @trunc_intro
        trunc_zero
        (@RawCubeFaceCode p n)
        (@raw_cube_comp p q n g raw))
    f;

// Functions into a set form a set, permitting the outer public recursion.
symbol cube_face_code_function_is_set
  [p q n : τ Nat_grpd]
  : τ (IsSetGrpd
      (@Function_grpd (@CubeFaceCode p q) (@CubeFaceCode p n)))
≔ @is_trunc_pi
    trunc_zero
    (@CubeFaceCode p q)
    (λ _ : τ (@CubeFaceCode p q), @CubeFaceCode p n)
    (λ _ : τ (@CubeFaceCode p q), @cube_face_code_is_set p n);

/*
  Public structural substitution. Both operands are eliminated only into
  classified sets; visible {L,R,*} inputs reduce to raw substitution.
*/
symbol cube_face_comp
  [p q n : τ Nat_grpd]
  (g : τ (@CubeFaceCode q n))
  (f : τ (@CubeFaceCode p q))
  : τ (@CubeFaceCode p n)
≔ (@trunc_rec_ambient
      trunc_zero
      (@RawCubeFaceCode q n)
      (@Function_grpd (@CubeFaceCode p q) (@CubeFaceCode p n))
      (@cube_face_code_function_is_set p q n)
      (λ raw : τ (@RawCubeFaceCode q n),
        λ f0 : τ (@CubeFaceCode p q),
          @cube_face_comp_from_raw p q n raw f0)
      g) f;
